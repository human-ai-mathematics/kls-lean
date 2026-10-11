# Context handoff correction

The user clarified that the requested automatic context handoff concerns Codex, not Claude.
The mistakenly created Claude heartbeat was removed. The superseded paragraph follows verbatim.

The user authorized automatic replacement of the Claude conversation as its context fills.
Prepare a checked handoff at 85 percent context use; at 90 percent, wait for the current task
to finish, verify its artifacts and terminal state, then create one replacement conversation
in the same checkout. Confirm its identity and task receipt before transferring the sole
Claude editor role. A thread heartbeat checks this every 15 minutes; dispatch-time checks
remain part of the live controller. `CLAUDE-CONTEXT-HANDOFF.json` in the scratch workspace
records the current conversation, task, thresholds and migration state. Five-hour and weekly
account usage are separate; switching conversations does not reset them. Reset cards remain
the user's action.
