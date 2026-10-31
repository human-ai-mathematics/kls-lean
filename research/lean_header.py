#!/usr/bin/env python3
"""Parse the header of a Lean source file: `module`, `prelude` and its import directives.

Grammar (Lean v4.35, `Lean.Elab.ParseImportsFast.main`)::

    [module] [prelude] ([public] [meta] import [all] <Module>)*

Between header directives, comments (including module documentation) are trivia. Inside one
directive, from a modifier or `import`/`all` keyword to the mandatory first module name, the
trivia is exactly Lean's import-header `whitespace` (ParseImportsFast.lean:97-119): spaces and
newlines, `--` line comments and nested `/- -/` block comments, but no tab and no doc comment
(`/--`, `/-!` are tokens there, line 116). `keywordCore` consumes that whitespace after every
keyword (line 123), so `import`, `all` and the first module may sit on different lines.
Lexing stops at the first token that does not continue the header, so declaration bodies are
never lexed. Lean v4.35 reads exactly one module per `import` (`main`, lines 237-244); further
modules on the SAME line as the first one are accepted only for older sources, each as its own
edge, and never across a line break. Anything else that could hide an import fails
closed with `HeaderError`: an unterminated comment, a malformed module name, a dangling
modifier, `public`/`meta`/`all` outside a `module` file, `public import all`, or an
import directive after the header has ended.

Callers decide how modifiers matter. Import-graph, build-closure and cache tools keep
every edge (public, private, `meta` and `import all`); `meta` only changes which IR is
loaded, and `all` only widens visibility.
"""
from __future__ import annotations

from dataclasses import dataclass
import re

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")
KEYWORDS = frozenset({"module", "prelude", "public", "meta", "import", "all"})
# Words that may precede a (misplaced) import directive; used only to fail closed.
_DIRECTIVE_WORDS = frozenset({"public", "meta", "private", "all"})


# Compiled artifacts Lean v4.35 writes per source (`Lean.Environment.writeModule`, Environment.lean
# 1902-1918; Lake `Module.computeArtifacts`): a `module` source has the exported `.olean` plus
# `.olean.server`, `.olean.private`, `.ir.sig` and `.ir`; a non-module source only `.olean`.
# Importing a module reads `.olean.server` and `.olean.private` unconditionally
# (`readModuleDataPartsOfMod`, Environment.lean:2079-2093), while a missing `.ir.sig` is skipped
# silently (`readIRPartsOfMod`); replay views and cache checks therefore require all five.
MODULE_ARTIFACTS = (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir")
NONMODULE_ARTIFACTS = (".olean",)


def required_artifacts(source: str) -> tuple[str, ...]:
    """The compiled artifacts a source must have, from its own header (HeaderError if unparsable)."""
    return MODULE_ARTIFACTS if parse_header(source).is_module else NONMODULE_ARTIFACTS


class HeaderError(ValueError):
    """The header cannot be parsed without risking a missed import."""


@dataclass(frozen=True)
class LeanImport:
    module: str
    public: bool = False
    meta: bool = False
    all: bool = False

    def directive(self) -> str:
        words = (["public"] if self.public else []) + (["meta"] if self.meta else [])
        return " ".join([*words, "import", *(["all"] if self.all else []), self.module])


@dataclass(frozen=True)
class LeanHeader:
    is_module: bool
    prelude: bool
    imports: tuple[LeanImport, ...]
    end: int  # offset just past the last header token; `source[end:]` is the remaining file

    @property
    def modules(self) -> list[str]:
        return [item.module for item in self.imports]


def skip_trivia(source: str, i: int) -> int:
    """Skip whitespace, line comments and nested block (including doc) comments."""
    n = len(source)
    while i < n:
        if source[i].isspace():
            i += 1
        elif source.startswith("--", i):
            j = source.find("\n", i)
            i = n if j < 0 else j
        elif source.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if source.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise HeaderError("unterminated block comment in module header")
        else:
            break
    return i


def skip_directive_trivia(source: str, i: int) -> int:
    """Lean's import-header `whitespace` (ParseImportsFast.lean:97-119), used inside one directive.

    Newlines, `--` comments and nested `/- -/` comments are skipped; a tab is an error (line 103)
    and a doc comment ends the trivia because it is a token there (line 116).
    """
    n = len(source)
    while i < n:
        if source[i] == "\t":
            raise HeaderError("tabs are not allowed in an import directive")
        if source[i].isspace():
            i += 1
        elif source.startswith("--", i):
            j = source.find("\n", i)
            i = n if j < 0 else j
        elif source.startswith("/-", i) and not source.startswith(("/--", "/-!"), i):
            depth, i = 1, i + 2
            while i < n and depth:
                if source.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise HeaderError("unterminated block comment in an import directive")
        else:
            break
    return i


def _word(source: str, i: int):
    return IDENT.match(source, skip_trivia(source, i))


def _reject_misplaced_import(source: str, i: int) -> None:
    word = _word(source, i)
    while word and word.group() in _DIRECTIVE_WORDS:
        word = _word(source, word.end())
    if word and word.group() in {"import", "module", "prelude"}:
        raise HeaderError(f"header directive after the header ended: {source[word.start():word.start() + 60]!r}")


def parse_header(source: str) -> LeanHeader:
    is_module = prelude = False
    end = 0
    word = _word(source, 0)
    if word and word.group() == "module":
        is_module, end = True, word.end()
        word = _word(source, end)
    if word and word.group() == "prelude":
        prelude, end = True, word.end()
        word = _word(source, end)
    imports: list[LeanImport] = []
    while word:
        public = meta = False
        token = word
        for modifier in ("public", "meta"):
            if token and token.group() == modifier:
                position = skip_directive_trivia(source, token.end())
                if position >= len(source):
                    raise HeaderError("dangling import modifier at end of file")
                token = IDENT.match(source, position)
                public, meta = public or modifier == "public", meta or modifier == "meta"
        if not token or token.group() != "import":
            break  # e.g. `public section`, `meta def`: the header has ended before `word`
        # Mandatory first module: Lean's whitespace (any lines, comments) may precede it.
        k = skip_directive_trivia(source, token.end())
        import_all = False
        keyword = IDENT.match(source, k)
        if keyword and keyword.group() == "all":
            import_all, k = True, skip_directive_trivia(source, keyword.end())
        name = IDENT.match(source, k)
        if not name or name.group() in KEYWORDS:
            if k >= len(source) or not name:
                raise HeaderError(f"import directive without a module name: {source[k:k + 40]!r}")
            raise HeaderError(f"unsupported import syntax: {source[k:k + 40]!r}")
        names, j = [name.group()], name.end()
        # Legacy only: further modules on the same line as the first one.
        while True:
            k = skip_trivia(source, j)
            if k >= len(source) or "\n" in source[j:k]:
                break
            name = IDENT.match(source, k)
            if not name or name.group() in KEYWORDS:
                raise HeaderError(f"unsupported import syntax: {source[k:k + 40]!r}")
            names.append(name.group())
            j = name.end()
        if (public or meta or import_all) and not is_module:
            raise HeaderError("cannot use 'public', 'meta' or 'all' without 'module'")
        if public and import_all:
            raise HeaderError("cannot use 'all' with 'public import'")
        imports.extend(LeanImport(name, public, meta, import_all) for name in names)
        end = j
        word = _word(source, end)
    _reject_misplaced_import(source, end)
    return LeanHeader(is_module, prelude, tuple(imports), end)


def nonmodule_client(driver: str, leading_imports: list[str], *, allowed: set[str]) -> str:
    """Embed a committed tooling driver in a generated NON-module Lean client.

    A non-module root imports every module at the private level (Lean v4.35
    `Lean.Elab.processHeaderCore`), so generated audit and observation clients keep seeing
    private and generated declarations. The driver's own header (`module`, modifiers) is
    replaced by plain imports; its body is kept byte for byte. The driver may import only
    `allowed` modules, so the producer stays the only source of library imports.
    """
    header = parse_header(driver)
    unexpected = sorted(set(header.modules) - allowed)
    if header.prelude or unexpected:
        raise HeaderError(f"driver header must import only {sorted(allowed)}; found {unexpected or ['prelude']}")
    modules = list(dict.fromkeys([*leading_imports, *header.modules]))
    return "\n".join("import " + module for module in modules) + driver[header.end:]
