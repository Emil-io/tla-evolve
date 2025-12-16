#!/usr/bin/env bash
set -euo pipefail

# Usage:
#   ./run.sh <name> <iterations> [extra_args...]
# Examples:
#   ./run.sh distributed_mutex 50
#   ./run.sh missionaries-and-cannibals 120 --log-level DEBUG

NAME="${1:-distributed_mutex}"
ITERATIONS="${2:-10}"

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EXAMPLE_DIR="${ROOT_DIR}/examples/${NAME}"
PROGRAM="${EXAMPLE_DIR}/initial_program.tla"
EVALUATOR="${ROOT_DIR}/evaluator.py"
CONFIG="${ROOT_DIR}/config.yaml"
OUTPUT_DIR="${ROOT_DIR}/runs/${NAME}"

# Export EXAMPLE_DIR so the evaluator can find the TLC config
export TLA_EXAMPLE_DIR="${EXAMPLE_DIR}"

# Load environment variables from .env if present
if [[ -f "${ROOT_DIR}/.env" ]]; then
  echo "Loading environment from ${ROOT_DIR}/.env"
  set -a
  # Temporarily disable nounset to avoid errors on empty/unset variables in .env
  set +u
  # shellcheck source=/dev/null
  source "${ROOT_DIR}/.env"
  set -u
  set +a
fi


# Validate inputs
if [[ ! -d "${EXAMPLE_DIR}" ]]; then
  echo "Example not found: ${EXAMPLE_DIR}" >&2
  exit 1
fi
if [[ ! -f "${PROGRAM}" ]]; then
  echo "Program not found: ${PROGRAM}" >&2
  exit 1
fi
if [[ ! -f "${EVALUATOR}" ]]; then
  echo "Evaluator not found: ${EVALUATOR}" >&2
  exit 1
fi
if [[ ! -f "${CONFIG}" ]]; then
  echo "Config not found: ${CONFIG}" >&2
  exit 1
fi

mkdir -p "${OUTPUT_DIR}"

echo "Running example '${NAME}' for ${ITERATIONS} iterations..."
echo "Example directory: ${EXAMPLE_DIR}"
echo "Output directory: ${OUTPUT_DIR}"

uv run python "${ROOT_DIR}/openevolve/openevolve/cli.py" \
  "${PROGRAM}" \
  "${EVALUATOR}" \
  --config "${CONFIG}" \
  --output "${OUTPUT_DIR}" \
  --iterations "${ITERATIONS}" \
  "${@:3}"

