#!/usr/bin/env bash
# SMT soundness layer — end-to-end runner (spike-only test infrastructure).
#
# Provenance: stwo rev 5ea05973, PR #1425 (see ../SHA256-SOUNDNESS-FIX.md).
# Runs from a clean state: existing cargo gate -> mechanical AIR dump -> full z3 check matrix.
# Exits NONZERO on any Rust gate failure, any extraction/structural/ledger/sanity failure,
# any verdict != expectation, any unknown/timeout, or any SAT-model replay failure.
#
# DISCLOSURE GUARDRAIL: PR #1425 is open, unmerged and undisclosed. Nothing on this branch —
# including everything under smt/ — may be pushed to a public remote until the fix is disclosed
# per ../SHA256-SOUNDNESS-FIX.md. Do not soften.
set -euo pipefail
cd "$(dirname "$0")/.."                                    # sha256_sound_spike/

# 1. Existing gate stays green (acceptance #6). Rust prover-side is unchanged by this layer.
cargo test

# 2. Mechanical extraction: run the ACTUAL Eval::evaluate, dump JSON (panics -> nonzero on any
#    of the dump-time fidelity asserts: counts, set-diff, Round decode, numeric gates A/B).
mkdir -p smt/out
cargo run --bin dump_smt -- smt/out/air.json

# 3. z3 check matrix. Prefer `uv run --with z3-solver`; fall back to a local venv.
if command -v uv >/dev/null 2>&1; then
  uv run --with z3-solver python smt/check.py smt/out/air.json | tee smt/out/report.txt
else
  [ -d smt/.venv ] || { python3 -m venv smt/.venv && smt/.venv/bin/pip -q install z3-solver; }
  smt/.venv/bin/python smt/check.py smt/out/air.json | tee smt/out/report.txt
fi
# `set -o pipefail` above propagates check.py's exit code through the `tee`.
