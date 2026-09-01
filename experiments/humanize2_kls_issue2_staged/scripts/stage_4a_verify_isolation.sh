#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_4a_common.sh"

h2_temp_root="$(mktemp -d /private/tmp/h2-issue2-stage4a-isolation.XXXXXX)"
trap 'chmod -R u+rwX "$h2_temp_root" 2>/dev/null || true; rm -rf "$h2_temp_root"' EXIT
export H2_ISSUE2_STAGE4A_STATE_ROOT="$h2_temp_root/state"
h2_state_root="$(h2_stage4a_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_actor_codex_home="$h2_state_root/actor-codex-home"
h2_actor_runtime_tmp="$h2_state_root/actor-runtime-tmp"
h2_seatbelt="$h2_state_root/actor-seatbelt.sb"
h2_lean_bin_path="$(h2_stage4a_lean_bin)"
h2_main_checkout="$(h2_stage4a_main_checkout)"
h2_baseline_formalization="$(h2_stage4a_baseline_formalization_root)"

"$h2_stage4a_script_dir/stage_4a_reset_run_state.sh" >/dev/null
"$h2_stage4a_script_dir/stage_4a_verify_scaffold.sh" >/dev/null

h2_forbidden_experiment="$h2_stage4a_repo_root/formalization/FunctionalInequalities/Poincare.lean"
h2_forbidden_baseline="$h2_baseline_formalization/FunctionalInequalities/Poincare.lean"
h2_forbidden_compiled="$(h2_stage4a_kls_build_root)/FunctionalInequalities/Poincare.olean"
h2_forbidden_main="$h2_main_checkout/formalization/FunctionalInequalities/Poincare.lean"
h2_forbidden_basic="$h2_stage4a_repo_root/formalization/FunctionalInequalities/Basic.lean"
h2_forbidden_certificate="$h2_stage4a_repo_root/solutions/LemLinearTestLower.lean"
h2_forbidden_design="$h2_stage4a_repo_root/LEAN_DESIGN.md"
h2_forbidden_review="$h2_stage4a_repo_root/research/reviews/2026-08-29-lean-linear-test-semantic-followup.md"
h2_forbidden_knowledge="$h2_stage4a_repo_root/research/knowledge/lemmas.md"
h2_forbidden_handoff="$h2_stage4a_repo_root/docs/HUMANIZE2_LEAN_BASELINE_HANDOFF.md"
h2_forbidden_checklist="$h2_stage4a_experiment_root/review/issue2_stage_4a_human_checklist.md"
h2_forbidden_oracle="$h2_stage4a_experiment_root/oracle/stage_4a_reference.sha256"

for h2_forbidden in \
  "$h2_forbidden_experiment" \
  "$h2_forbidden_baseline" \
  "$h2_forbidden_compiled" \
  "$h2_forbidden_main" \
  "$h2_forbidden_basic" \
  "$h2_forbidden_certificate" \
  "$h2_forbidden_design" \
  "$h2_forbidden_review" \
  "$h2_forbidden_knowledge" \
  "$h2_forbidden_handoff" \
  "$h2_forbidden_checklist" \
  "$h2_forbidden_oracle"; do
  if [[ ! -f "$h2_forbidden" ]]; then
    echo "Stage 4A isolation probe target is absent: $h2_forbidden" >&2
    exit 1
  fi
done

(
  cd "$h2_actor_root"
  H2_FORBIDDEN_EXPERIMENT="$h2_forbidden_experiment" \
  H2_FORBIDDEN_BASELINE="$h2_forbidden_baseline" \
  H2_FORBIDDEN_COMPILED="$h2_forbidden_compiled" \
  H2_FORBIDDEN_MAIN="$h2_forbidden_main" \
  H2_FORBIDDEN_BASIC="$h2_forbidden_basic" \
  H2_FORBIDDEN_CERTIFICATE="$h2_forbidden_certificate" \
  H2_FORBIDDEN_DESIGN="$h2_forbidden_design" \
  H2_FORBIDDEN_REVIEW="$h2_forbidden_review" \
  H2_FORBIDDEN_KNOWLEDGE="$h2_forbidden_knowledge" \
  H2_FORBIDDEN_HANDOFF="$h2_forbidden_handoff" \
  H2_FORBIDDEN_CHECKLIST="$h2_forbidden_checklist" \
  H2_FORBIDDEN_ORACLE="$h2_forbidden_oracle" \
  H2_ACTOR_CODEX_HOME="$h2_actor_codex_home" \
  H2_ACTOR_RUNTIME_TMP="$h2_actor_runtime_tmp" \
    sandbox-exec -f "$h2_seatbelt" /bin/zsh --no-rcs -c '
      set -euo pipefail
      test -r AGENTS.md
      test -r TASK.md
      test -r AcceptedStage1A.lean
      test -r AcceptedStage1A.olean
      test -r AcceptedStage1B.lean
      test -r AcceptedStage1B.olean
      test -r AcceptedStage2A.lean
      test -r AcceptedStage2A.olean
      test -r AcceptedStage2B.lean
      test -r AcceptedStage2B.olean
      test -r AcceptedStage3.lean
      test -r AcceptedStage3.olean
      test -r CandidateStage4A.lean
      for target in \
        "$H2_FORBIDDEN_EXPERIMENT" \
        "$H2_FORBIDDEN_BASELINE" \
        "$H2_FORBIDDEN_COMPILED" \
        "$H2_FORBIDDEN_MAIN" \
        "$H2_FORBIDDEN_BASIC" \
        "$H2_FORBIDDEN_CERTIFICATE" \
        "$H2_FORBIDDEN_DESIGN" \
        "$H2_FORBIDDEN_REVIEW" \
        "$H2_FORBIDDEN_KNOWLEDGE" \
        "$H2_FORBIDDEN_HANDOFF" \
        "$H2_FORBIDDEN_CHECKLIST" \
        "$H2_FORBIDDEN_ORACLE" \
        "$H2_ACTOR_CODEX_HOME/config.toml"; do
        if /bin/cat "$target" >/dev/null 2>&1; then exit 41; fi
      done
      if { printf "%s\n" tamper >> AcceptedStage1A.lean; } 2>/dev/null; then exit 42; fi
      if { printf "%s\n" tamper >> AcceptedStage1A.olean; } 2>/dev/null; then exit 43; fi
      if { printf "%s\n" tamper >> AcceptedStage1B.lean; } 2>/dev/null; then exit 44; fi
      if { printf "%s\n" tamper >> AcceptedStage1B.olean; } 2>/dev/null; then exit 45; fi
      if { printf "%s\n" tamper >> AcceptedStage2A.lean; } 2>/dev/null; then exit 46; fi
      if { printf "%s\n" tamper >> AcceptedStage2A.olean; } 2>/dev/null; then exit 47; fi
      if { printf "%s\n" tamper >> AcceptedStage2B.lean; } 2>/dev/null; then exit 48; fi
      if { printf "%s\n" tamper >> AcceptedStage2B.olean; } 2>/dev/null; then exit 49; fi
      if { printf "%s\n" tamper >> AcceptedStage3.lean; } 2>/dev/null; then exit 50; fi
      if { printf "%s\n" tamper >> AcceptedStage3.olean; } 2>/dev/null; then exit 51; fi
      if touch actor-extra-file 2>/dev/null; then exit 52; fi
      if rm CandidateStage4A.lean 2>/dev/null; then exit 53; fi
      if touch "$H2_ACTOR_CODEX_HOME/tool-write-probe" 2>/dev/null; then exit 54; fi
      if touch "$H2_ACTOR_RUNTIME_TMP/tool-write-probe" 2>/dev/null; then exit 55; fi
      printf "%s\n" "-- candidate-only write probe" >> CandidateStage4A.lean
    '
)

"$h2_stage4a_script_dir/stage_4a_reset_actor_workspace.sh" >/dev/null
"$h2_stage4a_script_dir/stage_4a_verify_scaffold.sh" >/dev/null

python3 - \
  "$h2_stage4a_experiment_root/tests/fixtures/CandidateStage4A.lean.known_good" \
  "$h2_actor_root/CandidateStage4A.lean" <<'PY'
from pathlib import Path
import sys

Path(sys.argv[2]).write_bytes(Path(sys.argv[1]).read_bytes())
PY
(
  cd "$h2_actor_root"
  LEAN_PATH="$(h2_stage4a_actor_lean_path "$h2_actor_root")" \
    sandbox-exec -f "$h2_seatbelt" "$h2_lean_bin_path" CandidateStage4A.lean >/dev/null
)
"$h2_stage4a_script_dir/stage_4a_verify_candidate.sh" "$h2_actor_root" >/dev/null

CODEX_HOME="$h2_actor_codex_home" \
TMPDIR="$h2_actor_runtime_tmp" \
H2_STAGE4A_ACTOR_SEATBELT="$h2_seatbelt" \
H2_STAGE4A_ACTOR_ROOT="$h2_actor_root" \
  python3 - <<'PY'
import json
import os
import subprocess

process = subprocess.Popen(
    ["sandbox-exec", "-f", os.environ["H2_STAGE4A_ACTOR_SEATBELT"], "codex", "app-server", "--stdio"],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    text=True,
    env=os.environ,
    cwd=os.environ["H2_STAGE4A_ACTOR_ROOT"],
)
assert process.stdin is not None
assert process.stdout is not None
process.stdin.write(
    json.dumps(
        {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {"clientInfo": {"name": "stage4a-isolation-probe", "version": "0"}},
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

python3 -m unittest "$h2_stage4a_experiment_root/tests/test_stage_4a_audit_actor_trace.py" \
  >/dev/null 2>&1
echo "Stage 4A isolation passed: exact thirteen-entry fixture visible; all five accepted source/compiled pairs immutable; hidden KLS/oracle/design/review/knowledge/handoff/client state denied; candidate-only writes, accepted dependencies, upstream Lean, and Codex available"
