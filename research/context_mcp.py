"""Read-only MCP 2.3.0 stdio adapter; no build, network, or arbitrary-path tools."""
from __future__ import annotations
import argparse
import sys
from pathlib import Path
from .project_context import ContextError, ProjectContext

def build_server(context: ProjectContext):
    from mcp.server import MCPServer
    from mcp.types import ToolAnnotations
    server = MCPServer("kls-project-context")
    annotation = ToolAnnotations(readOnlyHint=True, destructiveHint=False, openWorldHint=False)
    def call(method, *args):
        try:
            return method(*args)
        except (ContextError, TypeError, ValueError, RecursionError) as exc:
            return {"error": str(exc)[:300], "read_only": True}

    @server.tool(name="project_snapshot", annotations=annotation)
    def project_snapshot(view: str = "head", revision: str | None = None) -> dict:
        """Capture head, index, or coherent worktree; revision requires a full commit ID."""
        return call(context.project_snapshot, view, revision)

    @server.tool(name="project_status", annotations=annotation)
    def project_status(snapshot: str, offset: int = 0, limit: int = 20) -> dict:
        """Page recorded paper, task and certificate facts with exact source references."""
        return call(context.project_status, snapshot, offset, limit)

    @server.tool(name="verification_status", annotations=annotation)
    def verification_status(snapshot: str, scope: str = "full", offset: int = 0, limit: int = 20) -> dict:
        """Compare local receipt claims with complete source bindings; never run verification."""
        return call(context.verification_status, snapshot, scope, offset, limit)

    @server.tool(name="claim_explain", annotations=annotation)
    def claim_explain(snapshot: str, claim: str) -> dict:
        """Find a literal registry claim and optional source-bound compiler observation."""
        return call(context.claim_explain, snapshot, claim)

    @server.tool(name="changes_review", annotations=annotation)
    def changes_review(base: str, snapshot: str) -> dict:
        """Compare digest maps against a full commit ID and list recorded checks."""
        return call(context.changes_review, base, snapshot)

    @server.tool(name="work_next", annotations=annotation)
    def work_next(snapshot: str) -> dict:
        """Read current handoff work and literature priorities as recorded human intent."""
        return call(context.work_next, snapshot)

    @server.resource("project://kls/{commit}/handoff")
    def handoff(commit: str) -> str:
        """Read an immutable HANDOFF.md at a full commit ID; clipping is explicit."""
        try:
            return context.handoff_resource(commit)
        except ContextError as exc:
            return "Unavailable: " + str(exc)
    return server

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True)
    args = parser.parse_args(argv)
    build_server(ProjectContext(Path(args.repo))).run(transport="stdio")
    return 0

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ContextError, RuntimeError) as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(2)
