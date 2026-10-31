#!/usr/bin/env python3
"""Check owned source headings, live Markdown navigation and current scope summaries.

This is a local documentation gate. It neither elaborates Lean nor decides mathematical
proof status. Canonical literature records and explicit source bindings remain authoritative.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import subprocess
from urllib.parse import unquote, urlsplit

import module_inventory

ROOT = Path(__file__).resolve().parents[1]
CONFIG = Path("research/progress/documentation-checks.json")
TICK = chr(96)
SCOPE_START = "<!-- BEGIN CURRENT LETWIN SOURCE SCOPE -->"
SCOPE_END = "<!-- END CURRENT LETWIN SOURCE SCOPE -->"
HANDOFF_START = "<!-- BEGIN CURRENT MAINTENANCE -->"
HANDOFF_END = "<!-- END CURRENT MAINTENANCE -->"


@dataclass(frozen=True)
class Link:
    label: str
    target: str
    line: int
    start: int
    end: int


def lean_comments(text: str) -> tuple[str, list[tuple[int, str, bool]]]:
    """Mask nested comments/strings, retaining offsets and physical line numbers."""
    chars = list(text)
    comments = []
    i = 0
    while i < len(text):
        if text.startswith(("--", "/-"), i):
            start = i
            doc = text.startswith("/-!", i)
            if text.startswith("--", i):
                end = text.find("\n", i)
                i = len(text) if end < 0 else end
            else:
                i += 2
                depth = 1
                while i < len(text) and depth:
                    if text.startswith("/-", i):
                        depth += 1
                        i += 2
                    elif text.startswith("-/", i):
                        depth -= 1
                        i += 2
                    else:
                        i += 1
            comments.append((text.count("\n", 0, start) + 1, text[start:i], doc))
            for j in range(start, i):
                if chars[j] != "\n":
                    chars[j] = " "
        elif text[i] == '"':
            start = i
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            for j in range(start, min(i, len(text))):
                if chars[j] != "\n":
                    chars[j] = " "
        else:
            i += 1
    return "".join(chars), comments


def declaration_lines(text: str) -> dict[str, list[int]]:
    """Resolve explicit declaration headers, including namespaces and named sections."""
    code, _ = lean_comments(text)
    namespace = ""
    frames: list[str] = []
    result: dict[str, list[int]] = {}
    pattern = re.compile(
        r"^(?:(?:private|protected|noncomputable|unsafe|partial|public|meta|nonrec)\s+)*"
        r"(?:theorem|lemma|def|abbrev|structure|class|inductive)\s+([^\s({\[:=]+)"
    )
    # Lean v4.35 section syntax: `[@[expose]] [public] [noncomputable] [meta] section [name]`.
    section_pattern = re.compile(
        r"^(?:@\[[^\]]*\]\s*)?(?:(?:public|noncomputable|meta)\s+)*section(?:\s|$)")
    for number, line in enumerate(code.splitlines(), 1):
        ns = re.match(r"^namespace\s+(\S+)", line)
        section = section_pattern.match(line)
        if ns:
            frames.append(namespace)
            name = ns[1]
            namespace = name[7:] if name.startswith("_root_.") else ".".join(
                filter(None, (namespace, name)))
        elif section:
            frames.append(namespace)
        elif re.match(r"^end(?:\s|$)", line):
            if frames:
                namespace = frames.pop()
        match = pattern.match(line)
        if match:
            name = match[1]
            full = name[7:] if name.startswith("_root_.") else ".".join(
                filter(None, (namespace, name)))
            result.setdefault(full, []).append(number)
    return result


def mask_fences(text: str) -> str:
    output = []
    fence = None
    for line in text.splitlines(keepends=True):
        match = re.match(r"^\s*(" + TICK + r"{3,}|~{3,})", line)
        if match:
            if fence is None:
                fence = match[1][0]
            elif fence == match[1][0]:
                fence = None
            output.append("".join("\n" if c == "\n" else " " for c in line))
        elif fence:
            output.append("".join("\n" if c == "\n" else " " for c in line))
        else:
            output.append(line)
    return "".join(output)


def markdown_links(text: str) -> list[Link]:
    """Read inline destinations with balanced parentheses and reference definitions."""
    source = mask_fences(text)
    links = []
    i = 0
    while i < len(source):
        if source[i] == "\\":
            i += 2
            continue
        if source[i] == TICK:
            j = i
            while j < len(source) and source[j] == TICK:
                j += 1
            close = source.find(source[i:j], j)
            i = close + j - i if close >= 0 else j
            continue
        if source[i] != "[":
            i += 1
            continue
        start = i
        close = source.find("]", i + 1)
        if close < 0:
            break
        label = source[i + 1:close]
        if "\n" in label or "[" in label:
            i += 1
            continue
        if source[close + 1:close + 2] == "(":
            j = close + 2
            depth = 1
            angle = False
            while j < len(source) and depth:
                c = source[j]
                if c == "\\":
                    j += 2
                    continue
                if c == "<":
                    angle = True
                elif c == ">":
                    angle = False
                elif not angle and c == "(":
                    depth += 1
                elif not angle and c == ")":
                    depth -= 1
                j += 1
            if depth:
                i = close + 1
                continue
            raw = source[close + 2:j - 1].strip()
            target = raw[1:raw.find(">")] if raw.startswith("<") else re.split(
                r"""\s+["']""", raw, maxsplit=1)[0]
            links.append(Link(label, target, source.count("\n", 0, start) + 1,
                              close + 2, j - 1))
            i = j
        elif re.fullmatch(r" {0,3}", source[source.rfind("\n", 0, start) + 1:start]):
            ref = re.match(r":\s*(\S+)", source[close + 1:])
            if ref:
                links.append(Link(label, ref[1], source.count("\n", 0, start) + 1,
                                  close + 1 + ref.start(1), close + 1 + ref.end(1)))
            i = close + 1
        else:
            i = close + 1
    return links


def heading_ids(text: str) -> set[str]:
    ids = set(re.findall(r"""<a\s+(?:id|name)=["']([^"']+)""", text, re.I))
    counts: Counter[str] = Counter()
    for line in mask_fences(text).splitlines():
        match = re.match(r"^\s{0,3}#{1,6}\s+(.+?)\s*#*\s*$", line)
        if not match:
            continue
        title = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", match[1])
        title = re.sub(r"<[^>]*>", "", title).strip().lower()
        slug = "".join(c for c in title if c.isalnum() or c in "_- ").replace(" ", "-")
        count = counts[slug]
        counts[slug] += 1
        ids.add(slug + (f"-{count}" if count else ""))
    return ids


def visible_files(root: Path) -> list[str]:
    paths = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
        cwd=root, text=True).split("\0")
    return sorted({name for name in paths if name and (root / name).is_file()})


def resolve_local(root: Path, document: str, target: str) -> tuple[Path, str] | None:
    parsed = urlsplit(target)
    if parsed.scheme or parsed.netloc:
        return None
    source = root / document
    path = (source.parent / unquote(parsed.path)).resolve() if parsed.path else source.resolve()
    if not path.is_relative_to(root.resolve()):
        raise ValueError(f"{document}: nonlocal destination {target}")
    return path, unquote(parsed.fragment)


def check_headings(root: Path, names: list[str], exceptions: list[dict]) -> list[str]:
    errors = []
    allowed = {(x["source"], x["heading"]): x for x in exceptions}
    if len(allowed) != len(exceptions):
        errors.append("Duplicate compact-heading exception")
    seen = set()
    for name in names:
        if not name.startswith("formalization/FunctionalInequalities/") or not name.endswith(".lean"):
            continue
        _, comments = lean_comments((root / name).read_text())
        for first_line, raw, doc in comments:
            if not doc:
                continue
            body = raw[3:-2]
            lines = body.splitlines()
            fenced = mask_fences(body).splitlines()
            for i, line in enumerate(fenced):
                heading = line.strip()
                if not re.match(r"^#{1,6}\s+", heading):
                    continue
                if i + 1 >= len(lines) or not lines[i + 1].strip():
                    continue
                if re.match(r"^#{1,6}\s+", lines[i + 1].strip()):
                    continue
                key = (name, heading)
                if key in allowed:
                    seen.add(key)
                else:
                    errors.append(f"{name}:{first_line + i}: heading must end before a blank line "
                                  f"or comment boundary: {heading}")
    for key, entry in allowed.items():
        if not entry.get("reason"):
            errors.append(f"{key[0]}: heading exception needs its reviewed reason")
        if key not in seen:
            errors.append(f"{key[0]}: stale compact-heading exception: {key[1]}")
    return errors


def check_maintenance(root: Path, names: list[str], policy: dict) -> list[str]:
    """Keep reviewed source hygiene and audit ownership separate from mathematical status."""
    errors = []
    allowed = {(x["source"], x["option"], x["declaration"]): x
               for x in policy["linter_exceptions"]}
    if len(allowed) != len(policy["linter_exceptions"]):
        errors.append("Duplicate declaration-local linter exception")
    seen = set()
    known_lean = {name for name in names if name.endswith(".lean")}

    def reference_issue(source: str, reference: str) -> str | None:
        references = [reference]
        while any(re.search(r"\{[^{}]+\}", item) for item in references):
            expanded = []
            for item in references:
                group = re.search(r"\{([^{}]+)\}", item)
                if group:
                    expanded.extend(item[:group.start()] + part.strip() + item[group.end():]
                                    for part in group[1].split(","))
                else:
                    expanded.append(item)
            references = expanded
        for item in references:
            if item.startswith("Mathlib/") and (root / "formalization/.lake/packages/mathlib" / item).is_file():
                continue
            candidates = [root / item, root / module_inventory.LIBRARY / item,
                          (root / source).parent / item]
            relative = {path.resolve().relative_to(root).as_posix() for path in candidates
                        if path.resolve().is_relative_to(root)}
            if relative & known_lean:
                continue
            matches = sorted(name for name in known_lean if name.endswith("/" + item))
            if not matches:
                return f"missing source-file reference: {item}"
            if len(matches) > 1:
                return (f"ambiguous source-file reference: {item}; use an explicit owning path "
                        f"instead of {', '.join(matches)}")
        return None

    text_suffixes = {".lean", ".md", ".py", ".tex", ".json", ".yaml", ".yml", ".toml",
                     ".cff", ".bib", ".mmd", ".txt"}
    for name in names:
        path = root / name
        if path.suffix not in text_suffixes or name.startswith("formalization/vendor/"):
            continue
        text = path.read_text()
        if "\x00" in text or "\ufffd" in text:
            errors.append(f"{name}: NUL or replacement character in owned text")
        if not name.endswith(".lean"):
            continue
        for glyph in policy.get("forbidden_lookalikes", []):
            if glyph in text:
                errors.append(f"{name}: unreviewed lookalike character U+{ord(glyph):04X}")
        raw = path.read_bytes()
        if b"\r" in raw:
            errors.append(f"{name}: use Unix line endings")
        for number, line in enumerate(text.splitlines(), 1):
            if "\t" in line or line != line.rstrip():
                errors.append(f"{name}:{number}: tab or trailing whitespace")
            semicolon = line.find(";")
            if semicolon > 0 and line[semicolon - 1] == " ":
                errors.append(f"{name}:{number}: whitespace before semicolon")
        if not name.startswith("formalization/FunctionalInequalities/"):
            continue
        code, comments = lean_comments(text)
        module_comments = [comment for _, comment, is_doc in comments if is_doc]
        if not module_comments or not module_comments[0][3:-2].strip():
            errors.append(f"{name}: missing module summary (module documentation is absent or empty)")
        for line, comment, _ in comments:
            if re.search(r"\(\d{4}-\d{2}-\d{2}\s+candidate\)", comment):
                errors.append(f"{name}:{line}: obsolete dated candidate label")
            for reference in re.finditer(r"`([^`\n]*\.lean)`", comment):
                if issue := reference_issue(name, reference[1]):
                    location = line + comment.count("\n", 0, reference.start())
                    errors.append(f"{name}:{location}: {issue}")
        if re.search(r"(?m)^\s*#print\s+axioms\b", code):
            errors.append(f"{name}: production axiom report belongs in an audit client")
        declarations = sorted((line, declaration) for declaration, positions in
                              declaration_lines(text).items() for line in positions)
        for match in re.finditer(r"(?m)^\s*set_option\s+(linter\.[\w.]+)\s+false\b([^\n]*)", code):
            line = code.count("\n", 0, match.start()) + 1
            if match[2].strip() != "in":
                errors.append(f"{name}:{line}: linter suppression must be declaration-local")
            next_declaration = next((decl for start, decl in declarations if start > line), "")
            key = (name, match[1], next_declaration)
            if key not in allowed:
                errors.append(f"{name}:{line}: unreviewed linter exception for {next_declaration}")
            else:
                seen.add(key)
    for key, entry in allowed.items():
        if not entry.get("reason"):
            errors.append(f"{key[0]}: linter exception needs its interface-preservation reason")
        if key not in seen:
            errors.append(f"{key[0]}: stale linter exception for {key[2]}")
    for binding in policy["audit_reports"]:
        path = root / binding["audit"]
        if not path.is_file():
            errors.append(f"Missing narrow axiom-report owner: {binding['audit']}")
            continue
        code, _ = lean_comments(path.read_text())
        pattern = r"#print\s+axioms\s+" + re.escape(binding["declaration"]) + r"(?=\s|$)"
        if not re.search(pattern, code):
            errors.append(f"{binding['audit']}: missing migrated axiom report for "
                          f"{binding['declaration']}")
    return errors


def current_scope(root: Path, config: dict) -> str:
    record = json.loads((root / "research/progress/literature.json").read_text())
    paper = next(x for x in record["papers"] if x["id"] == config["paper"])
    items = {x["id"]: x for x in paper["lemma_map"]["items"]}
    lines = [SCOPE_START, "## Current Letwin paper-source scope", "",
             "The current paper-source results use " + TICK + "n > 0" + TICK +
             ", bounded open convex nonempty " + TICK + "K" + TICK + ",",
             "a potential smooth on an open neighborhood of its closure and convex on " +
             TICK + "K" + TICK + ",",
             "and the normalized isotropic law. They apply to every admissible moment potential.",
             "The source declarations retain the complete hypotheses and quantifier order.", "",
             "| Source item | Reviewed relation | Current declarations |",
             "| --- | --- | --- |"]
    for entry in config["items"]:
        item = items[entry["id"]]
        if item["relation"] != entry["relation"]:
            raise ValueError(f"Current scope: review the changed relation for {entry['id']}")
        declarations = {x["name"]: x for x in item["declarations"]}
        targets = []
        for name in entry["declarations"]:
            declaration = declarations[name]
            path = root / declaration["source"]
            if name not in declaration_lines(path.read_text()):
                raise ValueError(f"Current scope declaration missing from source: {name}")
            relative = Path(os.path.relpath(path, root / Path(config["document"]).parent))
            targets.append(f"[{TICK}{name}{TICK}]({relative.as_posix()})")
        lines.append(f"| {item['locator']} | {item['relation']} | " + "<br>".join(targets) + " |")
    lines.extend(["", "The earlier strong-class and variational constructions below retain their own",
                  "assumptions and intermediate gaps. Those gaps do not downgrade these paper-source",
                  "conclusions, and the paper-source conclusions do not supply every intermediate",
                  "construction of the earlier variational route.", SCOPE_END])
    return "\n".join(lines)


def maintenance_scope(config: dict) -> str:
    return "\n".join([
        HANDOFF_START,
        "## Current maintenance",
        "",
        *config["scope_lines"],
        f"See the [current source review]({config['review_map']}).",
        config["preservation"],
        config["next_step"],
        config.get("activity_scope", "No commit, push or remote certification is part of this maintenance."),
        HANDOFF_END,
    ])


def replace_block(text: str, start: str, end: str, expected: str) -> str:
    if text.count(start) != 1 or text.count(end) != 1:
        raise ValueError(f"Expected exactly one generated block: {start}")
    a, z = text.index(start), text.index(end) + len(end)
    return text[:a] + expected + text[z:]


def read_pointer(value, pointer: str):
    for part in pointer.strip("/").split("/"):
        part = part.replace("~1", "/").replace("~0", "~")
        if isinstance(value, list):
            value = next(x for x in value if x.get("id") == part[1:]) if part.startswith("@") else value[int(part)]
        else:
            value = value[part]
    return value


def navigation(root: Path, names: list[str], bindings: list[dict],
               *, write: bool = False) -> tuple[list[str], int]:
    errors = []
    links_by_document = {name: markdown_links((root / name).read_text())
                         for name in names if name.endswith(".md")}
    registered = {}
    replacements: dict[str, list[tuple[int, int, str]]] = {}
    checked = 0
    for binding in bindings:
        document, source = binding["document"], binding["source"]
        source_text = (root / source).read_text()
        declarations = declaration_lines(source_text)
        positions = declarations.get(binding["declaration"], [])
        if len(positions) != 1:
            errors.append(f"{source}: expected one declaration {binding['declaration']}, got {positions}")
            continue
        expected = positions[0]
        if "field" in binding:
            code, _ = lean_comments(source_text)
            fields = []
            for number, line in enumerate(code.splitlines()[expected:], expected + 1):
                if line.strip() and not line[0].isspace():
                    break
                if re.match(r"^\s+" + re.escape(binding["field"]) + r"\s*:", line):
                    fields.append(number)
            if len(fields) != 1:
                errors.append(f"{source}: expected one field {binding['field']} in "
                              f"{binding['declaration']}, got {fields}")
                continue
            expected = fields[0]
        matches = []
        for link in links_by_document.get(document, []):
            local = resolve_local(root, document, link.target)
            if (local and local[1] and local[0] == (root / source).resolve()
                    and link.label == binding["label"]):
                matches.append(link)
        if len(matches) != binding.get("occurrences", 1):
            errors.append(f"{document}: expected {binding.get('occurrences', 1)} link(s) "
                          f"for {binding['label']} to {source}, found {len(matches)}")
        for link in matches:
            key = (document, link.start)
            if key in registered:
                errors.append(f"{document}:{link.line}: duplicate declaration-link binding")
            registered[key] = binding
            checked += 1
            if urlsplit(link.target).fragment != f"L{expected}":
                if write:
                    target = link.target.split("#", 1)[0] + f"#L{expected}"
                    replacements.setdefault(document, []).append((link.start, link.end, target))
                else:
                    errors.append(f"{document}:{link.line}: {binding['label']} must point to "
                                  f"{source}#L{expected}, not {link.target}")
    for document, links in links_by_document.items():
        for link in links:
            local = resolve_local(root, document, link.target)
            if local and local[0].suffix == ".lean" and re.fullmatch(r"L\d+(?:-L\d+)?", local[1]):
                if (document, link.start) not in registered:
                    errors.append(f"{document}:{link.line}: unbound Lean declaration link: {link.target}")
    if write and not errors:
        for document, edits in replacements.items():
            path = root / document
            text = path.read_text()
            for a, z, target in sorted(edits, reverse=True):
                text = text[:a] + target + text[z:]
            path.write_text(text)
    return errors, checked


def check_documentation(root: Path, *, names: list[str] | None = None) -> tuple[list[str], dict]:
    root = root.resolve()
    names = visible_files(root) if names is None else names
    config = json.loads((root / CONFIG).read_text())
    if config["version"] != 1:
        raise ValueError("Unsupported documentation-check configuration")
    errors = check_headings(root, names, config["compact_headings"])
    errors.extend(check_maintenance(root, names, config["maintenance"]))
    data = module_inventory.inventory(root)
    errors.extend(data["errors"])
    directory = root / module_inventory.OUTPUT
    if not directory.is_file() or directory.read_text() != module_inventory.render(data):
        errors.append(f"Stale module directory: {module_inventory.OUTPUT}")
    count = 0
    for name in names:
        if not name.endswith(".md"):
            continue
        for link in markdown_links((root / name).read_text()):
            local = resolve_local(root, name, link.target)
            if local is None:
                continue
            path, fragment = local
            count += 1
            if not path.exists():
                errors.append(f"{name}:{link.line}: missing destination: {link.target}")
            elif fragment and path.is_file():
                span = re.fullmatch(r"L(\d+)(?:-L(\d+))?", fragment)
                if span:
                    first, last = int(span[1]), int(span[2] or span[1])
                    if not 1 <= first <= last <= len(path.read_text().splitlines()):
                        errors.append(f"{name}:{link.line}: line anchor out of range: {link.target}")
                elif path.suffix == ".md" and fragment not in heading_ids(path.read_text()):
                    errors.append(f"{name}:{link.line}: missing heading: {link.target}")
    nav_errors, bound = navigation(root, names, config["declaration_links"])
    errors.extend(nav_errors)
    scope = config["current_letwin_scope"]
    scope = {**scope, "document": Path(scope["document"])}
    expected = current_scope(root, scope)
    path = root / scope["document"]
    if replace_block(path.read_text(), SCOPE_START, SCOPE_END, expected) != path.read_text():
        errors.append(f"{scope['document']}: stale current Letwin scope block")
    handoff = config["handoff"]
    path = root / handoff["document"]
    if not (root / handoff["review_map"]).is_file():
        errors.append("Current maintenance source review is missing")
    if replace_block(path.read_text(), HANDOFF_START, HANDOFF_END,
                     maintenance_scope(handoff)) != path.read_text():
        errors.append(f"{handoff['document']}: stale current maintenance block")
    for entry in config["route_scope_notes"]:
        value = json.loads((root / entry["source"]).read_text())
        text = read_pointer(value, entry["pointer"])
        if ("prefix" in entry and not text.startswith(entry["prefix"])) or (
                "contains" in entry and entry["contains"] not in text):
            errors.append(f"{entry['source']}:{entry['pointer']}: missing route-specific gap scope")
    for entry in config["reviewed_scope_passages"]:
        if entry["required"] not in (root / entry["source"]).read_text():
            errors.append(f"{entry['source']}: review changed source-scope passage: {entry['reason']}")
    return errors, {"lean_modules": data["count"], "markdown_files": sum(
        name.endswith(".md") for name in names), "local_links": count, "bound_declaration_links": bound}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--write", action="store_true",
                        help="refresh only the canonical scope blocks and bound declaration links")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    try:
        if args.write:
            config = json.loads((root / CONFIG).read_text())
            names = visible_files(root)
            errors, _ = navigation(root, names, config["declaration_links"], write=True)
            if errors:
                raise ValueError("\n".join(errors))
            scope = config["current_letwin_scope"]
            scope = {**scope, "document": Path(scope["document"])}
            for name, start, end, expected in [
                (scope["document"], SCOPE_START, SCOPE_END, current_scope(root, scope)),
                (config["handoff"]["document"], HANDOFF_START, HANDOFF_END,
                 maintenance_scope(config["handoff"])),
            ]:
                path = root / name
                path.write_text(replace_block(path.read_text(), start, end, expected))
        errors, summary = check_documentation(root)
    except (OSError, ValueError, KeyError, StopIteration) as exc:
        print(f"FAIL: documentation inputs: {exc}")
        return 1
    for error in errors:
        print(f"FAIL: {error}")
    print("Documentation: " + ", ".join(f"{key}={value}" for key, value in summary.items()) +
          f"; {len(errors)} error(s).")
    return int(bool(errors))


if __name__ == "__main__":
    raise SystemExit(main())
