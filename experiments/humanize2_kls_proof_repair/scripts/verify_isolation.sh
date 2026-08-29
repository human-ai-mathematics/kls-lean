#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

h2_temp_root="$(mktemp -d /tmp/h2-proof-isolation.XXXXXX)"
trap 'rm -rf "$h2_temp_root"' EXIT
export H2_PROOF_STATE_ROOT="$h2_temp_root/state"
h2_state_root="$(h2_require_external_state_root)"
export H2_PROOF_STATE_ROOT="$h2_state_root"
h2_actor_root="$h2_state_root/actor-workspace"
h2_actor_codex_home="$h2_state_root/actor-codex-home"
h2_reviewer_codex_home="$h2_state_root/reviewer-codex-home"
h2_actor_runtime_tmp="$h2_state_root/actor-runtime-tmp"
h2_seatbelt="$h2_state_root/actor-seatbelt.sb"
h2_forbidden_oracle="$h2_proof_experiment_root/oracle/semantic_rubric.md"
h2_forbidden_ledger="$h2_proof_repo_root/research/kls/ledger.yaml"
h2_lean_bin_path="$(h2_lean_bin)"

"$h2_proof_script_dir/reset_run_state.sh" >/dev/null
"$h2_proof_script_dir/verify_scaffold.sh" >/dev/null
printf 'reviewer-only isolation marker\n' >"$h2_reviewer_codex_home/isolation-marker"

(
  cd "$h2_actor_root"
  H2_FORBIDDEN_ORACLE="$h2_forbidden_oracle" \
  H2_FORBIDDEN_LEDGER="$h2_forbidden_ledger" \
  H2_FORBIDDEN_REVIEWER_STATE="$h2_reviewer_codex_home/isolation-marker" \
    sandbox-exec -f "$h2_seatbelt" /bin/zsh --no-rcs -c '
      set -euo pipefail
      test -r AGENTS.md
      test -r TASK.md
      test -r CandidateProof.lean
      if cat "$H2_FORBIDDEN_ORACLE" >/dev/null 2>&1; then exit 41; fi
      if cat "$H2_FORBIDDEN_LEDGER" >/dev/null 2>&1; then exit 42; fi
      if cat "$H2_FORBIDDEN_REVIEWER_STATE" >/dev/null 2>&1; then exit 43; fi
      touch actor-write-probe
      rm actor-write-probe
    '
)

if sandbox-exec -f "$h2_seatbelt" \
  "$h2_lean_bin_path" "$h2_actor_root/CandidateProof.lean" >/dev/null 2>&1; then
  echo "broken proof unexpectedly compiled inside the actor sandbox" >&2
  exit 1
fi

perl -pi -e 's/Nat\.zero_add n/Nat.add_zero n/' "$h2_actor_root/CandidateProof.lean"
sandbox-exec -f "$h2_seatbelt" \
  "$h2_lean_bin_path" "$h2_actor_root/CandidateProof.lean"
"$h2_proof_script_dir/verify_candidate.sh" "$h2_actor_root" >/dev/null

CODEX_HOME="$h2_actor_codex_home" \
TMPDIR="$h2_actor_runtime_tmp" \
H2_PROOF_ACTOR_SEATBELT="$h2_seatbelt" \
H2_PROOF_ACTOR_ROOT="$h2_actor_root" \
  python3 - <<'PY'
import json
import os
import subprocess

process = subprocess.Popen(
    ["sandbox-exec", "-f", os.environ["H2_PROOF_ACTOR_SEATBELT"], "codex", "app-server", "--stdio"],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    text=True,
    env=os.environ,
    cwd=os.environ["H2_PROOF_ACTOR_ROOT"],
)
assert process.stdin is not None
assert process.stdout is not None
process.stdin.write(
    json.dumps(
        {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {"clientInfo": {"name": "isolation-probe", "version": "0"}},
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

echo "Seatbelt denied oracle, ledger, and reviewer-state reads; actor-local writes, Lean, and Codex passed"
