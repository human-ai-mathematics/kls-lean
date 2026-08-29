#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

h2_temp_root="$(mktemp -d /private/tmp/h2-issue2-stage1a-isolation.XXXXXX)"
trap 'rm -rf "$h2_temp_root"' EXIT
export H2_ISSUE2_STAGE1A_STATE_ROOT="$h2_temp_root/state"
h2_state_root="$(h2_issue2_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_actor_codex_home="$h2_state_root/actor-codex-home"
h2_actor_runtime_tmp="$h2_state_root/actor-runtime-tmp"
h2_seatbelt="$h2_state_root/actor-seatbelt.sb"
h2_lean_bin_path="$(h2_issue2_lean_bin)"
h2_main_checkout="$(h2_issue2_main_checkout)"
h2_baseline_formalization="$(h2_issue2_baseline_formalization_root)"

"$h2_issue2_script_dir/reset_run_state.sh" >/dev/null
"$h2_issue2_script_dir/verify_scaffold.sh" >/dev/null

h2_forbidden_experiment="$h2_issue2_repo_root/formalization/FunctionalInequalities/Basic.lean"
h2_forbidden_baseline="$h2_baseline_formalization/FunctionalInequalities/Basic.lean"
h2_forbidden_compiled="$(h2_issue2_kls_build_root)/FunctionalInequalities/Basic.olean"
h2_forbidden_main="$h2_main_checkout/formalization/FunctionalInequalities/Basic.lean"
h2_forbidden_solution="$h2_issue2_repo_root/solutions/README.md"
h2_forbidden_review="$h2_issue2_repo_root/research/reviews/2026-08-29-lean-linear-test-independent-semantic-audit.md"
h2_forbidden_ledger="$h2_issue2_repo_root/research/kls/ledger.yaml"
h2_forbidden_oracle="$h2_issue2_repo_root/experiments/humanize2_kls_statement_fidelity/oracle/semantic_rubric.md"

for h2_forbidden in \
  "$h2_forbidden_experiment" \
  "$h2_forbidden_baseline" \
  "$h2_forbidden_compiled" \
  "$h2_forbidden_main" \
  "$h2_forbidden_solution" \
  "$h2_forbidden_review" \
  "$h2_forbidden_ledger" \
  "$h2_forbidden_oracle"; do
  if [[ ! -f "$h2_forbidden" ]]; then
    echo "isolation probe target is absent: $h2_forbidden" >&2
    exit 1
  fi
done

(
  cd "$h2_actor_root"
  H2_FORBIDDEN_EXPERIMENT="$h2_forbidden_experiment" \
  H2_FORBIDDEN_BASELINE="$h2_forbidden_baseline" \
  H2_FORBIDDEN_COMPILED="$h2_forbidden_compiled" \
  H2_FORBIDDEN_MAIN="$h2_forbidden_main" \
  H2_FORBIDDEN_SOLUTION="$h2_forbidden_solution" \
  H2_FORBIDDEN_REVIEW="$h2_forbidden_review" \
  H2_FORBIDDEN_LEDGER="$h2_forbidden_ledger" \
  H2_FORBIDDEN_ORACLE="$h2_forbidden_oracle" \
  H2_ACTOR_CODEX_HOME="$h2_actor_codex_home" \
  H2_ACTOR_RUNTIME_TMP="$h2_actor_runtime_tmp" \
    sandbox-exec -f "$h2_seatbelt" /bin/zsh --no-rcs -c '
      set -euo pipefail
      test -r AGENTS.md
      test -r TASK.md
      test -r CandidateStage1A.lean
      for target in \
        "$H2_FORBIDDEN_EXPERIMENT" \
        "$H2_FORBIDDEN_BASELINE" \
        "$H2_FORBIDDEN_COMPILED" \
        "$H2_FORBIDDEN_MAIN" \
        "$H2_FORBIDDEN_SOLUTION" \
        "$H2_FORBIDDEN_REVIEW" \
        "$H2_FORBIDDEN_LEDGER" \
        "$H2_FORBIDDEN_ORACLE" \
        "$H2_ACTOR_CODEX_HOME/config.toml"; do
        if /bin/cat "$target" >/dev/null 2>&1; then exit 41; fi
      done
      if touch "$H2_ACTOR_CODEX_HOME/tool-write-probe" >/dev/null 2>&1; then exit 42; fi
      if touch "$H2_ACTOR_RUNTIME_TMP/tool-write-probe" >/dev/null 2>&1; then exit 43; fi
      touch actor-write-probe
      rm actor-write-probe
    '
)

if LEAN_PATH="$(h2_issue2_mathlib_lean_path)" \
  sandbox-exec -f "$h2_seatbelt" \
  "$h2_lean_bin_path" "$h2_actor_root/CandidateStage1A.lean" >/dev/null 2>&1; then
  echo "Stage 1A sentinel unexpectedly compiled inside the actor sandbox" >&2
  exit 1
fi

(
  cd "$h2_actor_root"
  sandbox-exec -f "$h2_seatbelt" /bin/zsh --no-rcs -c \
    'printf "%s\n" "import Mathlib.Analysis.Calculus.Gradient.Basic" "#check gradient" > LeanProbe.lean'
  LEAN_PATH="$(h2_issue2_mathlib_lean_path)" \
    sandbox-exec -f "$h2_seatbelt" "$h2_lean_bin_path" LeanProbe.lean >/dev/null
  sandbox-exec -f "$h2_seatbelt" /bin/rm LeanProbe.lean
)
"$h2_issue2_script_dir/verify_scaffold.sh" >/dev/null

CODEX_HOME="$h2_actor_codex_home" \
TMPDIR="$h2_actor_runtime_tmp" \
H2_STAGE1A_ACTOR_SEATBELT="$h2_seatbelt" \
H2_STAGE1A_ACTOR_ROOT="$h2_actor_root" \
  python3 - <<'PY'
import json
import os
import subprocess

process = subprocess.Popen(
    ["sandbox-exec", "-f", os.environ["H2_STAGE1A_ACTOR_SEATBELT"], "codex", "app-server", "--stdio"],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    text=True,
    env=os.environ,
    cwd=os.environ["H2_STAGE1A_ACTOR_ROOT"],
)
assert process.stdin is not None
assert process.stdout is not None
process.stdin.write(
    json.dumps(
        {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {"clientInfo": {"name": "stage1a-isolation-probe", "version": "0"}},
        }
    )
    + "\n"
)
process.stdin.flush()
while True:
    line = process.stdout.readline()
    if not line:
        stderr = process.stderr.read() if process.stderr is not None else ""
        raise SystemExit(f"Seatbelt-wrapped Codex app-server failed to initialize: {stderr}")
    message = json.loads(line)
    if message.get("id") == 1:
        if "result" not in message:
            raise SystemExit(f"Codex initialize failed: {message}")
        break
process.terminate()
PY

python3 -m unittest "$h2_issue2_experiment_root/tests/test_audit_actor_trace.py" >/dev/null
echo "Stage 1A isolation passed: exact fixture visible; KLS sources/oracle/review/ledger/client state denied; upstream Lean and Codex available"
