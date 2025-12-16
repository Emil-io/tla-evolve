## TLAEvolve — evolve TLA+/PlusCal with LLMs and TLC

TLAEvolve aims to automatically synthesize and improve TLA+/PlusCal specifications using an LLM-driven evolutionary loop with TLC as the ground-truth judge. Given a spec that defines invariants and properties as the rulebook, it searches for an algorithm/implementation that satisfies those constraints; candidates are checked with TLC and iterated on until a good solution emerges.

Built on top of `openevolve`, it combines island-based search and checkpointing with domain-specific evaluators that run TLC (and PlusCal translation when needed).

### Why this project

- Formal specs are precise but time-consuming to write and iterate on. We want a loop that proposes plausible changes and keeps only those that pass more checks.
- TLC provides an objective fitness function from the spec itself; LLMs supply creative, guided mutations.

### How it works (high level)

1. Seed: Provide a TLA+/PlusCal program and an evaluator that runs TLC with your `.cfg`.
2. Propose: The LLM suggests edits (diff-based by default).
3. Judge: The evaluator executes TLC, parses results, and returns `combined_score` plus artifacts.
4. Select + diversify: The search maintains diverse, high-scoring solutions and periodically migrates between islands.
5. Stop when done: Early-stop on reaching a target score or after N iterations; artifacts are saved.

### Prompts (fine-grained, file-based)

To make prompt iteration easier and more fine-grained, prompts are **not** embedded in `config.yaml`. Instead, we load prompt templates from the repo’s [`prompts/`](prompts/) folder (and many examples also provide per-task overrides under `examples/<task>/prompts/`).

---

## Prerequisites

- Java 11+ (17+ preferred)
- Python 3.10+ (repo uses `uv` for environment management)
- TLC tools JAR (`tla2tools.jar`)

### TLC JAR setup

1. Verify Java:

```bash
java -version
```

2. Get `tla2tools.jar` from `https://github.com/tlaplus/tlaplus/releases` (or use the copy at `tools/tla2tools.jar`).

3. Create `.env` in the repo root:

```
# If not set, defaults to tools/tla2tools.jar in this repo
TLA_TOOLS_JAR=/absolute/path/to/tla2tools.jar
OPENAI_API_KEY=YOUR_API_KEY
```

---

## Install

```bash
cd /path/to/tla-evolve
uv sync
```

---

## Quickstart

Run evolution (the evaluator handles PlusCal translation when needed) and write outputs to `runs/simple-counter`:

```bash
uv run openevolve-run \
  examples/simple-counter/initial_program.tla \
  evaluator.py \
  --config config.yaml \
  --output runs/simple-counter \
  --iterations 100 \
  --target-score 1
```

Visualize a checkpoint from that run:

```bash
uv run python openevolve/scripts/visualizer.py --path runs/simple-counter/checkpoints/checkpoint_1
```

---

## Examples

Each folder in [`examples/`](examples/) includes an `initial_program.tla` (the starting spec/program) and a TLC config (`*.cfg`) used by the evaluator.

- **[`examples/simple-counter/`](examples/simple-counter/)**: Minimal warm-up; evolve a small counter spec to satisfy invariants/properties.
- **[`examples/dijkstra-mutex/`](examples/dijkstra-mutex/)**: Dijkstra-style mutual exclusion; safety (mutex) and basic progress-style checks.
- **[`examples/ricart-agrawala-mutex/`](examples/ricart-agrawala-mutex/)**: Ricart–Agrawala distributed mutual exclusion; message-passing protocol constraints.
- **[`examples/producer-consumer-queue/`](examples/producer-consumer-queue/)**: Producer/consumer with a bounded queue; enqueue/dequeue correctness and invariants.
- **[`examples/lru-cache/`](examples/lru-cache/)**: LRU cache behavior; recency updates and consistency invariants.
- **[`examples/bipartite-matching/`](examples/bipartite-matching/)**: Bipartite matching; matching validity (no conflicts) and goal-related properties.
- **[`examples/missionaries-and-cannibals/`](examples/missionaries-and-cannibals/)**: Classic river-crossing puzzle; safety constraints and reaching a goal state.
