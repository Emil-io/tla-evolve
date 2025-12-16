import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, Optional, Tuple

from openevolve.evaluation_result import EvaluationResult


SUCCESS_MSG = "No error has been found"
MODULE_HEADER_RE = re.compile(r"^\s*-{2,}\s*MODULE\s+([A-Za-z0-9_]+)\s*-{2,}\s*$")
TRIVIAL_STATE_THRESHOLD = 3


def evaluate(program_path: str) -> EvaluationResult:
    try:
        return _evaluate_core(program_path)
    except Exception as exc:
        return EvaluationResult(
            metrics={"combined_score": 0.0},
            artifacts={"stdout": "", "stderr": str(exc), "status": "exception"},
        )


def _evaluate_core(program_path: str) -> EvaluationResult:
    project_root = Path(__file__).resolve().parent
    jar_path = os.getenv("TLA_TOOLS_JAR")
    if not jar_path or not Path(jar_path).exists():
        return EvaluationResult(
            metrics={"combined_score": 0.0},
            artifacts={"stdout": "", "stderr": "TLA tools jar not found", "status": "missing_jar"},
        )

    program_src = Path(program_path)
    if not program_src.exists():
        return EvaluationResult(
            metrics={"combined_score": 0.0},
            artifacts={"stdout": "", "stderr": "Program file not found", "status": "missing_file"},
        )

    with tempfile.TemporaryDirectory() as temp_dir_str:
        temp_dir = Path(temp_dir_str)

        module_name = _extract_module_name(program_src) or program_src.stem
        tla_filename = f"{module_name}.tla"
        tla_path = temp_dir / tla_filename
        shutil.copy2(program_src, tla_path)

        cfg_src = _resolve_cfg(program_src.parent)
        if cfg_src is None:
            example_dir = os.getenv("TLA_EXAMPLE_DIR")
            if example_dir:
                cfg_src = _resolve_cfg(Path(example_dir))
        if cfg_src is None:
            cfg_src = _find_example_cfg_by_module(module_name, project_root)
        if cfg_src is None:
            cfg_src = _resolve_cfg(project_root)
        if cfg_src is None:
            return EvaluationResult(
                metrics={"combined_score": 0.0},
                artifacts={
                    "stdout": "",
                    "stderr": f"No config file found for module '{module_name}'",
                    "status": "missing_config",
                },
            )

        cfg_path = temp_dir / "tlc_config.cfg"
        shutil.copy2(cfg_src, cfg_path)

        translator_stdout = ""
        translator_stderr = ""

        try:
            t_stdout, t_stderr = _translate_pluscal(
                work_dir=temp_dir, jar_path=jar_path, tla_filename=str(tla_path), timeout_seconds=180
            )
            translator_stdout = t_stdout or ""
            translator_stderr = t_stderr or ""
        except subprocess.CalledProcessError as exc:
            stdout_text = getattr(exc, "stdout", "") or ""
            stderr_text = getattr(exc, "stderr", "") or ""
            combined_out = stdout_text + stderr_text
            error_info = _analyze_translation_error(combined_out)
            try:
                ctx_lines = _extract_translation_error_context(
                    source_path=tla_path,
                    translator_output=combined_out,
                    context_radius=4,
                )
            except Exception:
                ctx_lines = []
            return EvaluationResult(
                metrics={"combined_score": 0.0},
                artifacts={
                    "stdout": stdout_text,
                    "stderr": stderr_text,
                    "status": "translation_error",
                    "primary_issue": error_info["primary_issue"],
                    "evidence": str(error_info["evidence"]),
                    "violated_properties": "[]",
                    "error_lines": str(ctx_lines or error_info["error_lines"]),
                }
            )
        except subprocess.TimeoutExpired as exc:
            stdout_text = getattr(exc, "stdout", "") or ""
            stderr_text = getattr(exc, "stderr", "") or "Timeout during translation"
            return EvaluationResult(
                metrics={"combined_score": 0.0},
                artifacts={
                    "stdout": stdout_text,
                    "stderr": stderr_text,
                    "status": "translation_timeout",
                    "primary_issue": "Translation timed out after 180 seconds",
                    "evidence": "[]",
                    "violated_properties": "[]",
                    "error_lines": "[]",
                }
            )

        try:
            tlc_ok, tlc_stdout, tlc_stderr = _run_tlc(
                work_dir=temp_dir, jar_path=jar_path, tla_filename=str(tla_path), cfg_path=cfg_path, timeout_seconds=1200
            )
        except subprocess.TimeoutExpired as exc:
            tlc_stdout = getattr(exc, "stdout", "") or ""
            tlc_stderr = getattr(exc, "stderr", "") or "Timeout during TLC"
            artifacts = _aggregate_artifacts(translator_stdout, translator_stderr, tlc_stdout, tlc_stderr)
            artifacts["status"] = "tlc_timeout"
            artifacts["primary_issue"] = "TLC timed out - model may be too large or have infinite behaviors"
            return EvaluationResult(metrics={"combined_score": 0.2}, artifacts=artifacts)

        score, status, analysis = _analyze_tlc_output(tlc_ok, tlc_stdout, tlc_stderr)

        artifacts = _aggregate_artifacts(translator_stdout, translator_stderr, tlc_stdout, tlc_stderr)
        artifacts["status"] = status
        artifacts["primary_issue"] = analysis.get("primary_issue", "")
        artifacts["evidence"] = str(analysis.get("evidence", []))
        artifacts["violated_properties"] = str(analysis.get("violated_properties", []))
        artifacts["error_lines"] = str(analysis.get("error_lines", []))

        return EvaluationResult(metrics={"combined_score": float(score)}, artifacts=artifacts)


def _analyze_translation_error(output: str) -> Dict:
    issues = []
    evidence = []
    error_lines = []

    if 'Expected "(" but found' in output:
        match = re.search(r'Expected "\(" but found "(\w+)".*line (\d+)', output, re.DOTALL)
        if match:
            found_token, line = match.groups()
            issues.append(f"PlusCal 'if' statement condition is missing required parentheses at line {line}.")
            evidence.append(f'Expected "(" but found "{found_token}"')
            error_lines.append(f"line {line}: change `if {found_token} = ...` to `if ({found_token} = ...) {{`")

    if 'Expected ":=" but found' in output:
        match = re.search(r'Expected ":=" but found "(\w+)".*line (\d+)', output, re.DOTALL)
        if match:
            found_token, line = match.groups()
            issues.append(f"PlusCal syntax error at line {line}. Likely mixing C-style braces with Pascal-style if/then/end if.")
            evidence.append(f'Expected ":=" but found "{found_token}"')
            error_lines.append(f"line {line}: Replace Pascal-style `if...then...end if` with C-style `if (...) {{ ... }}`")

    if "Empty statement list" in output:
        match = re.search(r'Empty statement list.*line (\d+)', output, re.DOTALL)
        line = match.group(1) if match else "unknown"
        issues.append(f"Procedure or block body is empty at line {line}. Add at least one statement (e.g., `label: skip;`).")
        evidence.append("Empty statement list")
        error_lines.append(f"line {line}: Add `labelName: skip;` inside the empty block")

    if "Missing label" in output:
        match = re.search(r'Missing label.*line (\d+)', output, re.DOTALL)
        line = match.group(1) if match else "unknown"
        issues.append(f"Missing label at line {line}. Statements after call/return/goto require labels.")
        evidence.append("Missing label")
        error_lines.append(f"line {line}: Add a label before the statement, e.g., `stepN:`")

    if "Unrecoverable error" in output:
        evidence.append("Unrecoverable error")
        match = re.search(r'--\s*(.+?)\n\s*line (\d+)', output)
        if match:
            error_msg, line = match.groups()
            evidence.append(f"-- {error_msg}")
            evidence.append(f"line {line}")

    if not issues:
        issues.append("PlusCal translation failed. Check syntax: ensure C-style braces, parenthesized conditions, and proper labels.")

    return {
        "primary_issue": " ".join(issues),
        "evidence": evidence,
        "error_lines": error_lines,
    }


def _extract_translation_error_context(*, source_path: Path, translator_output: str, context_radius: int = 3) -> list[str]:
    text = translator_output or ""
    line_nums: set[int] = set()

    for m in re.finditer(r"line\s+(\d+)\s*,\s*col\s+\d+\s*to\s*line\s+(\d+)\s*,\s*col\s+\d+", text, flags=re.IGNORECASE):
        line_nums.add(int(m.group(1)))
        line_nums.add(int(m.group(2)))
    for m in re.finditer(r"line\s+(\d+)\s*,\s*col\s+\d+", text, flags=re.IGNORECASE):
        line_nums.add(int(m.group(1)))
    for m in re.finditer(r"\bline\s+(\d+)\b", text, flags=re.IGNORECASE):
        try:
            line_nums.add(int(m.group(1)))
        except Exception:
            pass

    if not line_nums:
        return []

    try:
        with source_path.open("r", encoding="utf-8", errors="ignore") as f:
            src_lines = f.read().splitlines()
    except Exception:
        return []

    snippets: list[str] = []
    max_line = len(src_lines)
    for ln in sorted(line_nums):
        start = max(1, ln - context_radius)
        end = min(max_line, ln + context_radius)
        for cur in range(start, end + 1):
            tag = f"L{cur}: {src_lines[cur - 1]}"
            if not snippets or snippets[-1] != tag:
                snippets.append(tag)
        if snippets and snippets[-1] != "---":
            snippets.append("---")
    if snippets and snippets[-1] == "---":
        snippets.pop()
    return snippets


def _analyze_tlc_output(tlc_ok: bool, tlc_stdout: str, tlc_stderr: str) -> Tuple[float, str, Dict]:
    if tlc_ok and SUCCESS_MSG in tlc_stdout:
        return 1.0, "success", {
            "primary_issue": "No errors found. TLC verification passed.",
            "evidence": [SUCCESS_MSG],
            "violated_properties": [],
            "error_lines": [],
        }

    analysis = {
        "primary_issue": "",
        "evidence": [],
        "violated_properties": [],
        "error_lines": [],
    }

    combined = tlc_stdout + tlc_stderr

    metrics = _parse_tlc_state_counts(tlc_stdout)
    sany_ok = "SANY finished" in tlc_stdout
    states_generated = metrics.get("states_generated")
    distinct_states = metrics.get("distinct_states")
    if sany_ok and (
        (states_generated is not None and states_generated <= TRIVIAL_STATE_THRESHOLD)
        or (distinct_states is not None and distinct_states <= TRIVIAL_STATE_THRESHOLD)
    ):
        analysis["primary_issue"] = f"Trivial specification: TLC explored ≤ {TRIVIAL_STATE_THRESHOLD} states after successful parsing."
        ev_bits = []
        if states_generated is not None:
            ev_bits.append(f"states_generated={states_generated}")
        if distinct_states is not None:
            ev_bits.append(f"distinct_states={distinct_states}")
        if ev_bits:
            analysis["evidence"].append(", ".join(ev_bits))
        return 0.0, "trivial_spec", analysis

    if "Semantic error" in combined or "Parsing error" in combined or "SANY finished" not in tlc_stdout:
        analysis["primary_issue"] = "TLA+ semantic or parsing error after translation. Check generated TLA+ syntax."
        match = re.search(r'(Semantic|Parsing) error[^\n]*', combined)
        if match:
            analysis["evidence"].append(match.group(0))
        return 0.2, "syntax_error", analysis

    if "Deadlock reached" in combined:
        analysis["primary_issue"] = "TLC found a deadlock. The algorithm terminates in a state with no enabled actions."
        state_match = re.search(r'The behavior up to this point is:(.*?)(?=@!@!@|$)', combined, re.DOTALL)
        if state_match:
            states = re.findall(r'\d+: <[^>]+>.*?(?=\d+: <|\Z)', state_match.group(1), re.DOTALL)
            if states:
                last_state = states[-1][:500]
                analysis["evidence"].append(f"Final state before deadlock: {last_state}")
        analysis["error_lines"].append("Add an infinite stuttering loop at the end: `done: while (TRUE) { skip; };`")
        return 0.4, "deadlock", analysis

    invariant_match = re.search(r'Invariant (\w+) is violated', combined)
    if invariant_match:
        inv_name = invariant_match.group(1)
        analysis["violated_properties"].append(inv_name)
        analysis["primary_issue"] = f"Invariant {inv_name} is violated. The algorithm reaches an unsafe state."
        state_match = re.search(r'The behavior up to this point is:(.*?)(?=@!@!@|$)', combined, re.DOTALL)
        if state_match:
            analysis["evidence"].append(state_match.group(1)[:500])
        return 0.3, "invariant_violation", analysis

    property_match = re.search(r'(Property|Temporal property) (\w+) is violated', combined)
    if property_match:
        prop_name = property_match.group(2)
        analysis["violated_properties"].append(prop_name)
        analysis["primary_issue"] = f"Temporal property {prop_name} is violated."
        return 0.5, "property_violation", analysis

    if "Temporal properties were violated" in combined:
        analysis["primary_issue"] = "Liveness property violated. The algorithm doesn't reach the goal state."
        return 0.5, "liveness_violation", analysis

    if "Error:" in combined or tlc_stderr:
        error_match = re.search(r'Error:([^\n]+)', combined)
        if error_match:
            analysis["primary_issue"] = f"TLC error: {error_match.group(1).strip()}"
            analysis["evidence"].append(error_match.group(0))
        else:
            analysis["primary_issue"] = "TLC reported an unspecified error."
        return 0.2, "tlc_error", analysis

    analysis["primary_issue"] = "TLC did not report success but no specific error was identified."
    return 0.0, "unknown_error", analysis


def _translate_pluscal(*, work_dir: Path, jar_path: str, tla_filename: str, timeout_seconds: int) -> Tuple[str, str]:
    cmd = ["java", "-XX:+UseParallelGC", "-Dutil.debug=true", "-cp", jar_path, "pcal.trans", tla_filename]
    proc = subprocess.run(
        cmd,
        cwd=work_dir,
        capture_output=True,
        text=True,
        timeout=timeout_seconds,
        check=True,
    )
    return proc.stdout, proc.stderr


def _run_tlc(*, work_dir: Path, jar_path: str, tla_filename: str, cfg_path: Path, timeout_seconds: int) -> Tuple[bool, str, str]:
    cmd = [
        "java",
        "-XX:+UseParallelGC",
        "-Xmx1g",
        "-jar",
        jar_path,
        "-tool",
        "-config",
        str(cfg_path),
        str(tla_filename),
    ]

    proc = subprocess.run(
        cmd,
        cwd=work_dir,
        capture_output=True,
        text=True,
        timeout=timeout_seconds,
    )

    stdout_text = proc.stdout or ""
    stderr_text = proc.stderr or ""
    ok = SUCCESS_MSG in stdout_text
    return ok, stdout_text, stderr_text


def _resolve_cfg(search_dir: Path) -> Optional[Path]:
    for name in ("tlc.cfg", "tlc_config.cfg", "tcl_config.cfg", "config.cfg"):
        candidate = search_dir / name
        if candidate.exists():
            return candidate
    return None


def _find_example_cfg_by_module(module_name: str, project_root: Path) -> Optional[Path]:
    examples_dir = project_root / "examples"
    if not examples_dir.exists():
        return None

    for cfg_name in ("tlc.cfg", "tlc_config.cfg", "tcl_config.cfg", "config.cfg"):
        for root, _, _ in os.walk(examples_dir):
            root_path = Path(root)
            cfg_path = root_path / cfg_name
            if cfg_path.exists():
                initial_program = root_path / "initial_program.tla"
                if initial_program.exists():
                    found_module = _extract_module_name(initial_program)
                    if found_module == module_name:
                        return cfg_path
    return None


def _extract_module_name(tla_path: Path) -> Optional[str]:
    try:
        with tla_path.open("r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                match = MODULE_HEADER_RE.match(line)
                if match:
                    return match.group(1)
    except Exception:
        return None
    return None


def _aggregate_artifacts(translator_stdout: str, translator_stderr: str, tlc_stdout: str = "", tlc_stderr: str = "") -> Dict[str, str]:
    stdout_parts = []
    stderr_parts = []
    if translator_stdout:
        stdout_parts.append(translator_stdout)
    if tlc_stdout:
        stdout_parts.append(tlc_stdout)
    if translator_stderr:
        stderr_parts.append(translator_stderr)
    if tlc_stderr:
        stderr_parts.append(tlc_stderr)
    return {"stdout": "\n".join(stdout_parts), "stderr": "\n".join(stderr_parts)}


def _parse_tlc_state_counts(output: str) -> Dict[str, Optional[int]]:
    text = output or ""

    def _first_int(patterns) -> Optional[int]:
        for pat in patterns:
            m = re.search(pat, text, flags=re.IGNORECASE)
            if m:
                try:
                    return int(m.group(1).replace(",", "").strip())
                except Exception:
                    continue
        return None

    states_generated = _first_int([
        r"states?\s+generated[:\s]+([\d,]+)",
        r"([\d,]+)\s+states?\s+generated",
    ])
    distinct_states = _first_int([
        r"distinct\s+states?(?:\s+(?:found|explored))?[:\s]+([\d,]+)",
        r"([\d,]+)\s+distinct\s+states?",
    ])
    return {"states_generated": states_generated, "distinct_states": distinct_states}


if __name__ == "__main__":
    import sys

    if len(sys.argv) != 2:
        print("Usage: python evaluator.py <path/to/program.tla>")
        raise SystemExit(2)

    result = evaluate(sys.argv[1])
    metrics = result.metrics
    print({k: v for k, v in metrics.items()})

    artifacts = result.artifacts
    score = float(metrics.get("combined_score", 0.0))
    if score < 1.0:
        if artifacts:
            print("\n--- artifacts ---")
            for k, v in artifacts.items():
                if v:
                    print(f"{k}:\n{v}")
    else:
        print("\n✅ SUCCESS - TLC found no errors")
        stdout = artifacts.get("stdout")
        if stdout:
            for line in stdout.split("\n"):
                if "states generated" in line or "No error" in line:
                    print(line)
