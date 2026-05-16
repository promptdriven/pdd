import ast
import difflib
import glob
import logging
import os
import re
import json
import pathlib
import shlex
import subprocess
import requests
import tempfile
import sys
from typing import Optional, Tuple, Dict, Any, List, Set

import click
from rich.console import Console
from rich.panel import Panel
from rich.text import Text

# Relative imports for PDD package structure
from . import DEFAULT_STRENGTH, DEFAULT_TIME, EXTRACTION_STRENGTH # Assuming these are in __init__.py
from .construct_paths import construct_paths
from .preprocess import preprocess as pdd_preprocess
from .code_generator import code_generator as local_code_generator_func
from .incremental_code_generator import incremental_code_generator as incremental_code_generator_func
from .core.cloud import CloudConfig, get_cloud_timeout, get_cloud_request_timeout
from .python_env_detector import detect_host_python_executable
from .architecture_sync import (
    get_architecture_entry_for_prompt,
    has_pdd_tags,
    generate_tags_from_architecture,
)
from .architecture_registry import extract_modules
from .architecture_include_validation import validate_prompt_contract_context
from .validate_prompt_includes import validate_prompt_includes

console = Console()
logger = logging.getLogger(__name__)


class ArchitectureConformanceError(click.UsageError):
    """Typed exception raised when generated code violates the architecture contract.

    Subclass of :class:`click.UsageError` so existing call sites that catch
    ``click.UsageError`` continue to work unchanged. Carries structured fields
    so callers like ``pdd sync`` / ``agentic_sync_runner`` can build a repair
    directive and retry generation without parsing the message string.
    """

    def __init__(
        self,
        prompt_name: str,
        output_path: str,
        architecture_entry: Dict[str, Any],
        expected_symbols: List[str],
        found_symbols: List[str],
        missing_symbols: List[str],
        message: Optional[str] = None,
        total_cost: float = 0.0,
        model_name: str = "unknown",
        repair_directive: Optional[str] = None,
    ) -> None:
        self.prompt_name = prompt_name
        self.output_path = output_path or ""
        self.architecture_entry = architecture_entry or {}
        self.expected_symbols = list(expected_symbols)
        self.found_symbols = list(found_symbols)
        self.missing_symbols = list(missing_symbols)
        self.total_cost = float(total_cost or 0.0)
        self.model_name = model_name or "unknown"
        # Optional explicit repair directive (used by the <pdd-interface>
        # signature check where the prompt is the source of truth, not
        # architecture.json). When None, the property falls back to the
        # default architecture.json-oriented directive.
        self._repair_directive_override: Optional[str] = repair_directive
        if message is None:
            output_display = self.output_path or "<unknown>"
            message = (
                f"Architecture conformance error for {prompt_name}: "
                f"declared symbols missing from generated code: "
                f"{', '.join(self.missing_symbols)}. "
                f"Output: {output_display}. "
                f"Expected: {self.expected_symbols}. Found: {self.found_symbols}."
            )
        super().__init__(message)

    @property
    def repair_directive(self) -> str:
        """Multi-line, model-facing instruction naming the missing symbols."""
        if self._repair_directive_override:
            return self._repair_directive_override
        lines: List[str] = []
        lines.append(
            f"Architecture conformance error for {self.prompt_name}: "
            f"the generated code is missing required exports declared in architecture.json."
        )
        lines.append("Required missing exports:")
        for sym in self.missing_symbols:
            lines.append(f"- {sym}")
        lines.append("")
        lines.append(
            "Do not modify architecture.json. Do not remove existing valid exports."
        )
        if self.expected_symbols:
            lines.append(
                f"Expected interface symbols: {', '.join(self.expected_symbols)}."
            )
        if self.found_symbols:
            lines.append(
                f"Currently exported symbols: {', '.join(self.found_symbols)}."
            )
        return "\n".join(lines)


class PublicSurfaceRegressionError(click.UsageError):
    """Raised when generation removes public symbols from an existing module."""

    def __init__(
        self,
        prompt_name: str,
        output_path: str,
        removed_symbols: List[str],
        pre_surface_size: int,
        post_surface_size: int,
        changed_signatures: Optional[List[str]] = None,
        total_cost: float = 0.0,
        model_name: str = "unknown",
        repair_directive: Optional[str] = None,
    ) -> None:
        self.prompt_name = prompt_name
        self.output_path = output_path or ""
        self.removed_symbols = list(removed_symbols)
        self.changed_signatures = list(changed_signatures or [])
        self.pre_surface_size = int(pre_surface_size)
        self.post_surface_size = int(post_surface_size)
        self.total_cost = float(total_cost or 0.0)
        self.model_name = model_name or "unknown"
        self._repair_directive_override = repair_directive
        output_display = self.output_path or "<unknown>"
        super().__init__(
            f"Public surface regression for {prompt_name}:\n"
            f"removed: {', '.join(self.removed_symbols) if self.removed_symbols else '<none>'}\n"
            f"signature_changed: {', '.join(self.changed_signatures) if self.changed_signatures else '<none>'}\n"
            f"output: {output_display}\n"
            f"pre_surface_size: {self.pre_surface_size}\n"
            f"post_surface_size: {self.post_surface_size}"
        )

    @property
    def repair_directive(self) -> str:
        if self._repair_directive_override:
            return self._repair_directive_override
        lines = ["Public surface regression repair required."]
        if self.removed_symbols:
            lines.append("Restore these public symbols from the existing module:")
            for sym in self.removed_symbols:
                lines.append(f"- {sym}")
        if self.changed_signatures:
            lines.append("Restore compatible signatures for these public symbols:")
            for sym in self.changed_signatures:
                lines.append(f"- {sym}")
        lines.append(
            "Preserve backward-compatible public helpers unless the prompt lists "
            "the intended removals with BREAKING-CHANGE: remove <symbol>."
        )
        return "\n".join(lines)


class TestChurnError(click.UsageError):
    """Raised when generation rewrites too much of an existing test file."""

    def __init__(
        self,
        prompt_name: str,
        output_path: str,
        churn_ratio: float,
        threshold: float,
        pre_line_count: int,
        post_line_count: int,
        total_cost: float = 0.0,
        model_name: str = "unknown",
        repair_directive: Optional[str] = None,
    ) -> None:
        self.prompt_name = prompt_name
        self.output_path = output_path or ""
        self.churn_ratio = float(churn_ratio)
        self.threshold = float(threshold)
        self.pre_line_count = int(pre_line_count)
        self.post_line_count = int(post_line_count)
        self.total_cost = float(total_cost or 0.0)
        self.model_name = model_name or "unknown"
        self._repair_directive_override = repair_directive
        output_display = self.output_path or "<unknown>"
        super().__init__(
            f"Test churn threshold exceeded for {prompt_name}:\n"
            f"ratio: {self.churn_ratio:.2f}\n"
            f"threshold: {self.threshold:.2f}\n"
            f"output: {output_display}\n"
            f"pre_line_count: {self.pre_line_count}\n"
            f"post_line_count: {self.post_line_count}"
        )

    @property
    def repair_directive(self) -> str:
        if self._repair_directive_override:
            return self._repair_directive_override
        return (
            "Test churn repair required.\n"
            f"- Keep the existing broad test coverage in "
            f"{self.output_path or '<unknown>'}.\n"
            f"- Reduce unrelated rewrites below the configured churn threshold "
            f"({self.threshold:.2f}); current churn is {self.churn_ratio:.2f}.\n"
            "- Add or update only tests needed for the prompt change."
        )


# --- Helper Functions ---
def _parse_llm_bool(value: str) -> bool:
    """Parse LLM boolean value from string."""
    if not value:
        return True
    llm_str = str(value).strip().lower()
    if llm_str in {"0", "false", "no", "off"}:
        return False
    else:
        return llm_str in {"1", "true", "yes", "on"}

def _env_flag_enabled(name: str) -> bool:
    """Return True when an env var is set to a truthy value."""
    value = os.environ.get(name)
    if value is None:
        return False
    return str(value).strip().lower() in {"1", "true", "yes", "on"}


# Match a YAML front matter block: opening ``---`` on line 1, then any
# content, then a closing ``---`` on its own line. We anchor to the start
# of the string and require both fences to terminate with a newline so a
# stray ``---`` that never closes does NOT eat the entire prompt body.
# ``re.DOTALL`` so ``.`` matches newlines inside the block. Tolerates LF
# or CRLF line endings, a leading UTF-8 BOM, trailing whitespace on the
# fence lines, and a closing fence that is the final line of the file
# (``\Z``). This mirrors ``_parse_front_matter`` so both helpers agree on
# what counts as front matter — otherwise a CRLF or BOM prompt could
# leave ``BREAKING-CHANGE:`` metadata visible to the directive parser.
_YAML_FRONT_MATTER_RE = re.compile(
    r"\A﻿?---[ \t]*\r?\n.*?\r?\n---[ \t]*(?:\r?\n|\Z)",
    re.DOTALL,
)


def _strip_yaml_front_matter(prompt_content: Optional[str]) -> str:
    """Return ``prompt_content`` with a leading YAML front matter block stripped.

    Per the PR #1012 contract, BREAKING-CHANGE: opt-outs must come from the
    prompt BODY — not from metadata. The stripped form is what every
    BREAKING-CHANGE parser must see so that an indented directive inside
    front matter cannot whitelist surface removals or test-churn rewrites.

    The block must begin with ``---`` on line 1 (after an optional UTF-8
    BOM) and close with a ``---`` line. CRLF line endings, mixed line
    endings, trailing whitespace on the fence line, and a closing fence
    that is the final line of the file (no trailing newline) are all
    accepted — these match what ``_parse_front_matter`` already handles.
    An unterminated opening fence is left alone so we never silently
    swallow the entire prompt body.
    """
    if not prompt_content:
        return ""
    match = _YAML_FRONT_MATTER_RE.match(prompt_content)
    if match is None:
        # A leading UTF-8 BOM with NO front matter still needs stripping so
        # downstream BREAKING-CHANGE: scans see a clean body — otherwise a
        # BOM-only prompt would skip the fence but retain the BOM ahead of
        # the first directive line.
        if prompt_content.startswith("﻿"):
            return prompt_content[1:]
        return prompt_content
    return prompt_content[match.end():]


def _prompt_has_breaking_change_marker(prompt_content: Optional[str]) -> bool:
    """Return True when the prompt explicitly opts into breaking changes."""
    body = _strip_yaml_front_matter(prompt_content)
    return bool(body and "BREAKING-CHANGE:" in body)


# Match a BREAKING-CHANGE: directive only when it starts a line (optionally
# indented). Buried prose like "see the BREAKING-CHANGE: marker doc" must NOT
# trip the opt-out parsers, so the marker must be the first non-whitespace
# token on its line.
_BREAKING_CHANGE_DIRECTIVE_RE = re.compile(
    r"^[ \t]*BREAKING-CHANGE:[ \t]*(?P<directive>.*)$",
    re.MULTILINE,
)

# A symbol token in a BREAKING-CHANGE directive is a bare or wrapped
# identifier (optionally dotted for `Class.method`). Wrappers may be a
# backtick, single quote, or double quote — they MUST match on both sides
# (no `"old_helper'`). Prose words with embedded whitespace cannot match —
# the directive accepts a delimited symbol list, not arbitrary prose. We
# allow a leading verb (the action) to be stripped before this regex runs
# over the tail.
_DIRECTIVE_SYMBOL_RE = re.compile(
    r"^[ \t]*"
    r"(?P<wrap>[`'\"])?"
    r"(?P<symbol>[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)"
    r"(?(wrap)(?P=wrap))"
    r"[ \t]*$"
)


def _iter_breaking_change_directives(prompt_content: Optional[str]) -> List[str]:
    """Return the directive tails of anchored BREAKING-CHANGE: lines.

    Only lines whose first non-whitespace tokens are ``BREAKING-CHANGE:`` are
    treated as directives — buried mid-line markers (e.g. instructional prose
    naming the marker by example) are intentionally ignored so a line like
    ``Use BREAKING-CHANGE: remove old_helper to opt out`` does NOT register as
    a real directive.

    A leading YAML front matter block is stripped before the scan via
    :func:`_strip_yaml_front_matter` so that an indented directive inside
    metadata cannot opt the prompt out of the public-surface or
    test-churn gates. Opt-outs come from the prompt BODY only.
    """
    body = _strip_yaml_front_matter(prompt_content)
    if not body:
        return []
    return [
        match.group("directive").strip()
        for match in _BREAKING_CHANGE_DIRECTIVE_RE.finditer(body)
    ]


def _parse_breaking_change_symbols(directive_tail: str) -> Set[str]:
    """Parse a comma-separated list of identifier symbols from a directive tail.

    The tail is the text AFTER the action verb (e.g. after ``remove`` /
    ``rename`` / ``change signature``). We only accept tokens that look like
    bare or backticked Python identifiers (optionally dotted). Tokens with
    embedded whitespace are rejected so prose like ``to opt out`` does not
    leak in as a whitelist.
    """
    if not directive_tail:
        return set()
    # Drop a trailing sentence-terminator so "remove old_helper." parses cleanly.
    cleaned = directive_tail.strip()
    cleaned = cleaned.rstrip(".;:")
    if not cleaned:
        return set()
    symbols: Set[str] = set()
    for piece in cleaned.split(","):
        match = _DIRECTIVE_SYMBOL_RE.match(piece)
        if match:
            symbols.add(match.group("symbol"))
    return symbols


def _prompt_breaking_change_removed_symbols(prompt_content: Optional[str]) -> Set[str]:
    """Return public symbols explicitly listed for removal in BREAKING-CHANGE lines.

    Only anchored ``BREAKING-CHANGE:`` lines (first non-whitespace tokens on
    the line) participate. After the action verb (``remove``/``delete``/
    ``drop``/``rename``, including the gerund/plural variants) the remainder
    must be a comma-separated symbol list — prose tokens are rejected.
    """
    verb_re = re.compile(
        r"^(?:remov(?:e|es|ed|ing)|delet(?:e|es|ed|ing)|"
        r"drop(?:s|ped|ping)?|"
        r"renam(?:e|es|ed|ing))\b[ \t]*",
        re.IGNORECASE,
    )
    allowed: Set[str] = set()
    for directive in _iter_breaking_change_directives(prompt_content):
        match = verb_re.match(directive)
        if not match:
            continue
        tail = directive[match.end():]
        allowed.update(_parse_breaking_change_symbols(tail))
    return allowed


def _prompt_breaking_change_signature_symbols(prompt_content: Optional[str]) -> Set[str]:
    """Return public symbols explicitly listed for signature changes.

    Only anchored ``BREAKING-CHANGE:`` lines participate. The directive must
    start with a ``change`` verb followed by ``signature``/``signatures``/
    ``api``/``contract`` (e.g. ``change signature calculate``); we accept
    common verb tenses (``change``/``changes``/``changed``/``changing``).
    After the verb pair the remainder must be a comma-separated symbol list.
    """
    head_re = re.compile(
        r"^chang(?:e|es|ed|ing)\b[ \t]+"
        r"(?:signature|signatures|api|contract)\b[ \t]*",
        re.IGNORECASE,
    )
    allowed: Set[str] = set()
    for directive in _iter_breaking_change_directives(prompt_content):
        match = head_re.match(directive)
        if not match:
            continue
        tail = directive[match.end():]
        allowed.update(_parse_breaking_change_symbols(tail))
    return allowed


# Test-churn opt-out verbs. The marker doc and prompt body advertise both
# imperative ("rewrite tests") and gerund ("rewriting tests") wording, so the
# parser must accept both — anything documented in the directive emitted by
# `TestChurnError.repair_directive` must opt out the gate when echoed back.
_TEST_CHURN_OPT_OUT_RE = re.compile(
    r"\b("
    r"rewrit(?:e|es|ed|ing)|"
    r"replac(?:e|es|ed|ing)|"
    r"regenerat(?:e|es|ed|ing)|"
    r"overwrit(?:e|es|ing|ten)|"
    r"churn|"
    r"remov(?:e|es|ed|ing)|"
    r"drop(?:s|ped|ping)?"
    r")\b",
    re.IGNORECASE,
)
_TEST_CHURN_TARGET_RE = re.compile(r"\btests?\b", re.IGNORECASE)
# Separators that break the verb-object phrase. If any of these appears
# between the opt-out verb and `tests?`, the verb's nearest object is
# something OTHER than tests, so the directive must NOT opt out the gate.
# Examples: `rewrite docs and update tests` (the verb's object is "docs",
# not "tests"); `rewrite calculator, update tests` (comma breaks the phrase).
_TEST_CHURN_BRIDGE_BREAK_RE = re.compile(
    r"[,;]|\b(?:and|but|then|or|plus|also)\b",
    re.IGNORECASE,
)


def _prompt_allows_test_churn(prompt_content: Optional[str]) -> bool:
    """Return True only for explicit test rewrite/churn breaking-change directives.

    Only anchored ``BREAKING-CHANGE:`` directive lines count: prose that
    mentions the marker mid-line (e.g. instructional text referring to it)
    must NOT silently disable the test-churn gate. The directive must also
    pair an opt-out verb (imperative or gerund — ``rewrite``/``rewriting``/
    ``replace``/``replacing`` etc.) with the ``test``/``tests`` object: the
    parser scans every opt-out verb match, and requires that ``tests?``
    appear in the SAME verb-object phrase (no comma, semicolon, or
    conjunction like ``and``/``but``/``then``/``or`` between the verb
    and ``tests?``). That way:

    - ``BREAKING-CHANGE: rewriting the failing tests`` opts out (verb's
      object IS tests).
    - ``BREAKING-CHANGE: rewrite the test suite for new helper`` opts out
      (verb's object IS tests; trailing prose after a noun phrase is fine).
    - ``BREAKING-CHANGE: rewrite docs and update tests`` does NOT opt out
      (``rewrite``'s object is ``docs``; ``and`` breaks the phrase before
      ``tests``, and ``update`` is not in the opt-out verb list).
    - ``BREAKING-CHANGE: drop foo and rewrite tests`` DOES opt out (the
      second verb ``rewrite`` directly governs ``tests``).
    """
    for directive in _iter_breaking_change_directives(prompt_content):
        for verb_match in _TEST_CHURN_OPT_OUT_RE.finditer(directive):
            tail = directive[verb_match.end():]
            target_match = _TEST_CHURN_TARGET_RE.search(tail)
            if not target_match:
                continue
            bridge = tail[: target_match.start()]
            if _TEST_CHURN_BRIDGE_BREAK_RE.search(bridge):
                # A separator/conjunction breaks the verb-object phrase, so
                # `tests?` belongs to a DIFFERENT verb than the opt-out one.
                continue
            return True
    return False


def _is_python_generation(language: Optional[str], output_path: Optional[str]) -> bool:
    detected = (language or "").lower()
    return detected in {"python", "py"} or bool(
        output_path and str(output_path).lower().endswith(".py")
    )


def _is_test_output_path(output_path: Optional[str]) -> bool:
    if not output_path:
        return False
    path = pathlib.Path(str(output_path))
    name = path.name
    lower_name = name.lower()
    js_like_test_suffixes = (
        ".test.ts",
        ".test.tsx",
        ".test.js",
        ".test.jsx",
        ".spec.ts",
        ".spec.tsx",
        ".spec.js",
        ".spec.jsx",
    )
    return (
        name.startswith("test_")
        or name.endswith("_test.py")
        or lower_name.endswith(js_like_test_suffixes)
        or any(part in {"tests", "__tests__"} for part in path.parts)
    )


def _collect_bound_module_names(tree: ast.Module) -> Set[str]:
    """Return the set of all module-level names bound by ``tree``.

    Captures every name a ``from X import *`` would see, regardless of
    underscore prefix — used to filter ``__all__`` entries down to ones
    that are actually defined. The same kinds of bindings as
    :func:`_snapshot_public_surface` (functions, classes, Assign,
    AnnAssign-with-value, Import, ImportFrom) but without the
    underscore-prefix filter.
    """
    bound: Set[str] = set()

    def _walk_target(target: ast.AST) -> None:
        if isinstance(target, ast.Name):
            bound.add(target.id)
        elif isinstance(target, (ast.Tuple, ast.List)):
            for elt in target.elts:
                _walk_target(elt)
        elif isinstance(target, ast.Starred):
            _walk_target(target.value)

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            bound.add(node.name)
        elif isinstance(node, ast.ClassDef):
            bound.add(node.name)
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                _walk_target(target)
        elif isinstance(node, ast.AnnAssign):
            if node.value is not None:
                _walk_target(node.target)
        elif isinstance(node, ast.Import):
            for alias in node.names:
                bound.add(alias.asname or alias.name.split(".", 1)[0])
        elif isinstance(node, ast.ImportFrom):
            for alias in node.names:
                if alias.name == "*":
                    continue
                bound.add(alias.asname or alias.name)
    return bound


def _extract_dunder_all(tree: ast.Module) -> Optional[Set[str]]:
    """Return module-level ``__all__`` names if declared as a clean literal list.

    Walks every top-level assignment to ``__all__`` in source order and
    tracks a "current parse" state matching Python runtime semantics
    (subsequent assignments override earlier ones — the LAST assignment
    wins):

    - ``__all__ = [...]`` / ``__all__ = (...)`` whose elements are all
      ``ast.Constant`` string literals → set state to that set of
      strings.
    - ``__all__ = sorted(...)`` / ``__all__ = X + Y`` / any other
      non-literal RHS → set state to ``None``. The value is computed at
      runtime so a static parser cannot trust it, and the heuristic
      ("non-underscore") falls back.
    - ``__all__ += [...]`` (``ast.AugAssign``) → set state to ``None``.
      AugAssign mutates the previous list in place; even when the RHS
      is a clean literal we cannot statically be sure what's in the
      target object at that point (it could have been computed earlier).
      The safest correct rule is "any AugAssign to __all__ → fall back".
    - Bound ``ast.AnnAssign`` (``__all__: list[str] = [...]``) →
      treated the same as a plain assignment.

    Returns ``None`` when no clean ``__all__`` literal survives to the
    end of the module, OR when ``__all__`` is never assigned at module
    scope. In either case the fallback "non-underscore" heuristic
    applies.
    """
    state: Optional[Set[str]] = None
    for node in tree.body:
        if isinstance(node, ast.AugAssign):
            target = node.target
            if isinstance(target, ast.Name) and target.id == "__all__":
                # AugAssign is opaque: fall back to heuristic.
                state = None
            continue

        targets: List[ast.AST] = []
        value: Optional[ast.AST] = None
        if isinstance(node, ast.Assign):
            targets = list(node.targets)
            value = node.value
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            targets = [node.target]
            value = node.value
        else:
            continue
        # Look for a target that is a plain `__all__` Name.
        is_dunder_all_target = any(
            isinstance(t, ast.Name) and t.id == "__all__" for t in targets
        )
        if not is_dunder_all_target or value is None:
            continue
        if not isinstance(value, (ast.List, ast.Tuple)):
            # Computed __all__ (e.g. sorted(...), X + Y, name reference).
            # The last assignment wins per Python runtime semantics, so
            # this OVERRIDES any prior clean literal — reset to None so
            # the heuristic falls back.
            state = None
            continue
        names: Set[str] = set()
        clean = True
        for elt in value.elts:
            if isinstance(elt, ast.Constant) and isinstance(elt.value, str):
                names.add(elt.value)
            else:
                clean = False
                break
        # Whether clean or dirty, this assignment overrides any prior
        # state. Clean literals replace state with the new set; dirty
        # literals (non-string elements like a Name reference inside the
        # list) reset to None because we cannot trust the runtime value.
        state = names if clean else None
    return state


def _snapshot_public_surface(code_text: str, language: str) -> Set[str]:
    """Collect public top-level functions/classes plus public class methods.

    Recurses into public nested classes so a method on ``Outer.Inner`` is
    recorded as ``Outer.Inner.method``; removing it would otherwise escape
    both the removed-symbol diff and the signature-change diff because the
    enclosing class ``Outer.Inner`` is unchanged.

    Module-level ``ast.Assign`` / ``ast.AnnAssign`` targets, ``ast.Import``
    aliases, and ``ast.ImportFrom`` aliases are ALSO captured as public
    surface — removing a re-export like ``import git`` or a public constant
    like ``PUBLIC_SETTING = ...`` is a real downstream-breaking change.

    When the module declares ``__all__`` as a clean list/tuple of string
    constants, that list is AUTHORITATIVE per Python semantics: a name is
    public if and only if it appears in ``__all__``, even if the name is
    underscore-prefixed (e.g. ``__all__ = ["_public_helper"]``). Symbols
    not in ``__all__`` are NOT considered part of the public surface when
    ``__all__`` is declared. If ``__all__`` is missing or malformed
    (computed expression, non-string elements), the fallback heuristic
    applies: capture top-level non-underscore names, skip private/dunder.
    ``from X import *`` contributes no fixed name and is ignored.
    """
    if (language or "").lower() not in {"python", "py"}:
        return set()
    try:
        tree = ast.parse(code_text or "")
    except SyntaxError:
        return set()

    dunder_all = _extract_dunder_all(tree)

    names: set[str] = set()

    def _walk_class(
        class_node: ast.ClassDef,
        qualname: str,
        include_underscore: bool = False,
    ) -> None:
        """Recursively add dotted names for class members.

        ``include_underscore=True`` is used when the enclosing top-level
        class was explicitly opted into the public surface via
        ``__all__``: in that case the user's intent is that the class
        and its members ARE the public API, so underscore-prefixed
        methods/nested classes are NOT silently excluded (consistent
        with the existing ``__all__`` semantics where listing an
        underscore-prefixed top-level name like ``_helper`` makes it
        public). Outside of ``__all__`` scope the previous heuristic
        applies and underscores filter out.
        """
        for child in class_node.body:
            if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                continue
            if not include_underscore and child.name.startswith("_"):
                continue
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                names.add(f"{qualname}.{child.name}")
            else:  # ast.ClassDef
                nested_qualname = f"{qualname}.{child.name}"
                names.add(nested_qualname)
                _walk_class(child, nested_qualname, include_underscore)

    if dunder_all is not None:
        # __all__ is authoritative. Names declared in __all__ that are
        # actually bound at module scope (anything in __all__ that isn't
        # defined would be a runtime ImportError on `from X import *`,
        # which is the module author's bug, not this gate's concern)
        # form the public surface — INCLUDING the recursively-walked
        # members of any class entry in __all__. Without that recursion
        # a removal like `Service.run` would slip past the gate even
        # though it's clearly part of the declared public class.
        class_defs: Dict[str, ast.ClassDef] = {
            node.name: node
            for node in tree.body
            if isinstance(node, ast.ClassDef)
        }
        bound = _collect_bound_module_names(tree)
        for name in dunder_all:
            if name not in bound:
                continue
            names.add(name)
            if name in class_defs:
                # User opted the whole class into __all__; treat its
                # members (including underscore-prefixed) as public.
                _walk_class(class_defs[name], name, include_underscore=True)
        return names

    def _add_assign_targets(target: ast.AST) -> None:
        """Walk an assignment target, adding public bare-name identifiers.

        Handles tuple/list unpacking (``a, b = foo()`` and ``[a, b] = foo()``)
        by recursing into element lists. Attribute/subscript targets are
        ignored — those mutate existing objects, they don't create a new
        module-level name.
        """
        if isinstance(target, ast.Name):
            if not target.id.startswith("_"):
                names.add(target.id)
        elif isinstance(target, (ast.Tuple, ast.List)):
            for elt in target.elts:
                _add_assign_targets(elt)
        elif isinstance(target, ast.Starred):
            _add_assign_targets(target.value)

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if not node.name.startswith("_"):
                names.add(node.name)
        elif isinstance(node, ast.ClassDef):
            if not node.name.startswith("_"):
                names.add(node.name)
                _walk_class(node, node.name)
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                _add_assign_targets(target)
        elif isinstance(node, ast.AnnAssign):
            # Only bound annotations bind a runtime module attribute: a bare
            # `PUBLIC_NAME: int` declaration is a type hint, not an export,
            # so it would create false-positive regressions when removed.
            # `PUBLIC_NAME: int = None` (explicit None value) still binds and
            # is captured because `node.value` is the `ast.Constant(None)`
            # node, not Python `None`.
            if node.value is not None:
                _add_assign_targets(node.target)
        elif isinstance(node, ast.Import):
            for alias in node.names:
                # ``import foo.bar`` binds the top-level package name ``foo``;
                # ``import foo.bar as baz`` binds ``baz``.
                exposed = alias.asname or alias.name.split(".", 1)[0]
                if exposed and not exposed.startswith("_"):
                    names.add(exposed)
        elif isinstance(node, ast.ImportFrom):
            for alias in node.names:
                # ``from X import *`` has alias.name == "*"; no fixed
                # identifier is bound, so it does not contribute.
                if alias.name == "*":
                    continue
                exposed = alias.asname or alias.name
                if exposed and not exposed.startswith("_"):
                    names.add(exposed)

    return names


def _diff_public_surface(pre: Set[str], post: Set[str]) -> List[str]:
    """Return public symbols present before generation but absent after it."""
    return sorted(set(pre) - set(post))


def _format_python_signature(node: ast.AST, *, skip_first: bool = False) -> str:
    """Return a stable public-call signature string for a function-like AST node."""
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return ""
    args = node.args
    parts: List[str] = []

    def add_arg(arg: ast.arg, default: Optional[ast.AST] = None) -> None:
        text = arg.arg
        if arg.annotation is not None:
            text += f": {ast.unparse(arg.annotation)}"
        if default is not None:
            text += f"={ast.unparse(default)}"
        parts.append(text)

    posonly = list(args.posonlyargs)
    regular = list(args.args)
    # ``skip_first=True`` drops the implicit receiver (``self`` /
    # ``cls``) so an instance method is compared receiver-stripped. The
    # receiver lives in posonly when present (rare — e.g. PEP 570
    # methods), otherwise in ``args.args``. Strip from the correct list
    # so the remaining count used for the ``/`` marker insertion below
    # stays accurate (external review PR #1015).
    if skip_first:
        if posonly:
            posonly = posonly[1:]
        elif regular:
            regular = regular[1:]
    positional = posonly + regular
    defaults: List[Optional[ast.AST]] = [None] * (
        len(positional) - len(args.defaults)
    ) + list(args.defaults)
    parts_before_positional = len(parts)
    for arg, default in zip(positional, defaults):
        add_arg(arg, default)
    # Emit a literal ``/`` separator IMMEDIATELY after the
    # positional-only group so ``def f(x, /, y)`` and ``def f(x, y)``
    # produce DIFFERENT signature snapshots — kwarg-only callers
    # (``f(x=1, y=2)``) succeed against the second but break against
    # the first, and the public-surface gate must catch the
    # regression. Mirror the ``*`` insertion below for ``kwonlyargs``.
    # Skip when no posonly args remain after ``skip_first`` (a
    # stripped lone-receiver posonly leaves zero, in which case the
    # function is effectively a regular method and no ``/`` is
    # needed). External review PR #1015.
    if posonly:
        parts.insert(parts_before_positional + len(posonly), "/")
    if args.vararg:
        text = "*" + args.vararg.arg
        if args.vararg.annotation is not None:
            text += f": {ast.unparse(args.vararg.annotation)}"
        parts.append(text)
    elif args.kwonlyargs:
        parts.append("*")
    for arg, default in zip(args.kwonlyargs, args.kw_defaults):
        add_arg(arg, default)
    if args.kwarg:
        text = "**" + args.kwarg.arg
        if args.kwarg.annotation is not None:
            text += f": {ast.unparse(args.kwarg.annotation)}"
        parts.append(text)
    returns = ""
    if node.returns is not None:
        returns = f" -> {ast.unparse(node.returns)}"
    prefix = "async " if isinstance(node, ast.AsyncFunctionDef) else ""
    return f"{prefix}({', '.join(parts)}){returns}"


def _python_method_binding_kind(node: ast.AST) -> str:
    """Return the binding kind ('instance', 'staticmethod', 'classmethod',
    'property', 'property_accessor') for a class-body function-like node
    based on its decorators.

    Used by :func:`_snapshot_public_signatures` to prefix the captured
    signature string so that a binding-kind flip (e.g. ``def f(self, x)``
    becoming ``@staticmethod def f(x)``) is detected as a signature change
    even though the receiver-stripped parameter list is identical. Without
    this prefix, callers doing ``Class.f(1)`` would silently break across
    generations because the gate compared only normalized params.

    The ``property_accessor`` kind covers ``@x.setter`` / ``@x.getter`` /
    ``@x.deleter`` Attribute decorators — the caller is expected to merge
    these with the matching ``@property`` getter into a single combined
    snapshot per property name (see ``_walk_class``). Returning a
    dedicated kind for accessors prevents the last-write-wins overwrite
    that previously let a setter-decorated function be classified as a
    plain ``[instance]`` method.
    """
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return "instance"
    for decorator in getattr(node, "decorator_list", []):
        # Recognize property accessor decorators FIRST so ``@x.setter``
        # (an Attribute node with ``attr in {"setter","getter","deleter"}``)
        # is not silently flattened to ``instance`` by the generic
        # Attribute fallthrough below.
        if (
            isinstance(decorator, ast.Attribute)
            and decorator.attr in {"setter", "getter", "deleter"}
        ):
            return "property_accessor"
        name: Optional[str] = None
        if isinstance(decorator, ast.Name):
            name = decorator.id
        elif isinstance(decorator, ast.Attribute):
            name = decorator.attr
        elif isinstance(decorator, ast.Call):
            inner = decorator.func
            if isinstance(inner, ast.Name):
                name = inner.id
            elif isinstance(inner, ast.Attribute):
                name = inner.attr
        if name == "staticmethod":
            return "staticmethod"
        if name == "classmethod":
            return "classmethod"
        if name == "property":
            return "property"
    return "instance"


def _python_property_accessor_role(node: ast.AST) -> Optional[str]:
    """Return ``'getter'`` / ``'setter'`` / ``'deleter'`` when ``node`` is a
    property accessor — that is, decorated with ``@property`` (getter),
    ``@<name>.setter``, ``@<name>.getter``, or ``@<name>.deleter``.

    Returns ``None`` otherwise. Used by ``_walk_class`` to accumulate
    accessor roles per property name so the final snapshot reflects ALL
    accessors that exist (e.g. ``getter+setter``). Without this merge the
    setter would overwrite the getter entry and a rewrite that replaced
    the descriptor with a plain ``def x(self, value)`` could produce an
    identical snapshot string.
    """
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return None
    for decorator in getattr(node, "decorator_list", []):
        if isinstance(decorator, ast.Name) and decorator.id == "property":
            return "getter"
        if (
            isinstance(decorator, ast.Attribute)
            and decorator.attr in {"setter", "getter", "deleter"}
        ):
            return decorator.attr
    return None


def _snapshot_public_signatures(code_text: str, language: str) -> Dict[str, str]:
    """Collect signatures for public top-level functions, classes, and class methods.

    Recurses into public nested classes so a method like ``Outer.Inner.method``
    has its signature snapshot keyed by the same fully qualified name used in
    :func:`_snapshot_public_surface`. Without this the removed-symbol diff and
    the signature diff disagree on nested methods.

    When the module declares ``__all__`` as a clean list/tuple of string
    constants, that list is authoritative (same rule as
    :func:`_snapshot_public_surface`): a top-level function/class is
    captured only if it appears in ``__all__``, even when underscore-
    prefixed. Without that mirror the removed-symbol diff and the
    signature-drift diff would disagree on what is "public".

    Class methods are stored with a leading ``[<kind>]`` binding prefix
    (``[instance]``, ``[staticmethod]``, ``[classmethod]``, ``[property:...]``)
    so that a binding flip — e.g. ``def f(self, v)`` → ``@staticmethod def
    f(v)`` — produces a snapshot diff even when the receiver-stripped
    parameter list matches. Property descriptors carry a sorted accessor
    list (``[property:getter]``, ``[property:getter+setter]``, ...) so a
    rewrite that drops the descriptor in favor of a plain ``def x(self,
    value)`` cannot collide with the original snapshot.

    Top-level functions / async functions / classes carry a symbol-kind
    prefix (``[function]`` / ``[async_function]`` / ``[class]``) so a
    replacement that swaps a public class with a same-named function (or
    vice versa) is detected even when the receiver-stripped parameter
    list happens to match. Callers that ``Service()`` against a class and
    a function may both succeed on construction, but ``isinstance`` and
    subclass checks break — the kind prefix surfaces the regression
    before generation completes.
    """
    if (language or "").lower() not in {"python", "py"}:
        return {}
    try:
        tree = ast.parse(code_text or "")
    except SyntaxError:
        return {}

    dunder_all = _extract_dunder_all(tree)
    # When __all__ is authoritative, a top-level name is "public" iff it's
    # in __all__. Build a predicate that captures this.
    if dunder_all is not None:
        def _is_public_top_level(name: str) -> bool:
            return name in dunder_all
        # Classes opted into __all__ have their members treated as
        # public regardless of underscore prefix, consistent with the
        # __all__-authoritative branch in `_snapshot_public_surface`.
        include_methods_underscore_for_top_class = True
    else:
        def _is_public_top_level(name: str) -> bool:
            return not name.startswith("_")
        include_methods_underscore_for_top_class = False

    signatures: Dict[str, str] = {}

    def _walk_class(
        class_node: ast.ClassDef,
        qualname: str,
        include_underscore: bool = False,
    ) -> None:
        # Record the class itself with its constructor signature so that
        # ADDING a required `__init__` parameter is caught (#1012, P1.B).
        # The ``[class]`` kind prefix mirrors the top-level
        # function/async-function/class kind tagging so a replacement
        # that swaps the class for a function with a matching constructor
        # signature is still flagged.
        explicit_init: Optional[ast.AST] = None
        for child in class_node.body:
            if (
                isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
                and child.name == "__init__"
            ):
                explicit_init = child
                break
        if explicit_init is not None:
            class_signature = _format_python_signature(
                explicit_init, skip_first=True
            )
        else:
            class_signature = "()"
        signatures[qualname] = f"[class] {class_signature}"

        # First pass: accumulate property accessor roles per name so a
        # getter + setter combination collapses into ONE merged
        # ``[property:getter+setter]`` snapshot. Last-write-wins on the
        # dict (the previous behaviour) let ``@x.setter`` overwrite
        # ``@property`` and then misclassify the setter as ``[instance]``,
        # which let a real rewrite to ``def x(self, value)`` produce the
        # same snapshot string.
        property_accessors: Dict[str, Set[str]] = {}
        property_getter_nodes: Dict[str, ast.AST] = {}
        for child in class_node.body:
            if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            role = _python_property_accessor_role(child)
            if role is None:
                continue
            if not (include_underscore or not child.name.startswith("_")):
                continue
            property_accessors.setdefault(child.name, set()).add(role)
            # Remember the getter node so we can capture its parameter
            # signature in the final snapshot (the setter's ``(self,
            # value)`` shape is intentionally NOT used as the canonical
            # signature — accessors share the property identity but not
            # the param list).
            if role == "getter" and child.name not in property_getter_nodes:
                property_getter_nodes[child.name] = child

        for name, roles in property_accessors.items():
            sorted_roles = "+".join(sorted(roles))
            getter_node = property_getter_nodes.get(name)
            if getter_node is not None:
                getter_signature = _format_python_signature(
                    getter_node, skip_first=True
                )
            else:
                # ``@x.setter`` without an accompanying ``@property`` is
                # syntactically valid but unusual; fall back to ``()`` so
                # the entry still has a stable shape.
                getter_signature = "()"
            signatures[f"{qualname}.{name}"] = (
                f"[property:{sorted_roles}] {getter_signature}"
            )

        # Note: when a class body redefines the same name with mixed
        # binding kinds (e.g. plain ``def x`` followed by
        # ``@property def x``), the snapshot reflects the last *plain*
        # def encountered, not Python's runtime last-binding-wins
        # semantics. This is a rare source pattern; the gate may emit a
        # benign no-op diff in such cases. Documented for future
        # tightening.
        for child in class_node.body:
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                # __init__ already recorded above against ``qualname``;
                # do not re-add as ``qualname.__init__``.
                if child.name == "__init__":
                    continue
                # Property-decorated functions are handled in the
                # accumulator pass above — skip them here so a
                # last-write-wins overwrite cannot bury the merged
                # ``[property:...]`` entry under an ``[instance]``
                # snapshot from the setter.
                if _python_property_accessor_role(child) is not None:
                    continue
                binding_kind = _python_method_binding_kind(child)
                # ``staticmethod`` does NOT receive an implicit first arg
                # so its signature should NOT strip the leading positional.
                # ``classmethod`` / ``property`` / ``instance`` all bind
                # implicitly and skip the receiver. ``property`` getters
                # have a single ``self`` param that would otherwise vanish
                # from the snapshot, but the binding-kind prefix makes the
                # property-vs-method distinction observable on its own.
                skip_first = binding_kind != "staticmethod"
                if include_underscore or not child.name.startswith("_"):
                    base_signature = _format_python_signature(
                        child, skip_first=skip_first
                    )
                    signatures[f"{qualname}.{child.name}"] = (
                        f"[{binding_kind}] {base_signature}"
                    )
            elif isinstance(child, ast.ClassDef) and (
                include_underscore or not child.name.startswith("_")
            ):
                _walk_class(child, f"{qualname}.{child.name}", include_underscore)

    def _record_assignment_target(target: ast.AST) -> None:
        """Walk an assignment target, recording bare-name targets as ``[assignment]``.

        Mirrors :func:`_snapshot_public_surface`'s ``_add_assign_targets`` so
        an ``assignment ↔ def`` / ``assignment ↔ class`` kind flip becomes
        a snapshot diff in BOTH directions (``Foo = type(...)`` → ``def
        Foo()`` was previously invisible: surface kept ``Foo`` and the
        signatures dict had no ``Foo`` entry, so the new ``def Foo()``
        looked like an ADDED symbol, not a kind flip). Tuple/list/starred
        unpacking recurses; subscript/attribute targets are ignored
        (consistent with the surface helper — they mutate an existing
        object rather than binding a module attribute).
        """
        if isinstance(target, ast.Name):
            if _is_public_top_level(target.id):
                # Source order in the outer loop means a later ``def``/
                # ``class`` of the same name will overwrite this entry,
                # matching Python's last-binding-wins runtime semantics.
                signatures[target.id] = "[assignment]"
        elif isinstance(target, (ast.Tuple, ast.List)):
            for elt in target.elts:
                _record_assignment_target(elt)
        elif isinstance(target, ast.Starred):
            _record_assignment_target(target.value)

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and _is_public_top_level(node.name):
            # Top-level kind prefix so swapping a public class with a
            # same-named function (or vice versa) is detected even when
            # the normalized parameter list matches. ``[function]`` vs
            # ``[async_function]`` keeps an ``async def`` flip
            # observable too — callers awaiting the result of a former
            # sync function would otherwise silently see a coroutine.
            kind = "async_function" if isinstance(node, ast.AsyncFunctionDef) else "function"
            signatures[node.name] = (
                f"[{kind}] {_format_python_signature(node)}"
            )
        elif isinstance(node, ast.ClassDef) and _is_public_top_level(node.name):
            _walk_class(
                node,
                node.name,
                include_underscore=include_methods_underscore_for_top_class,
            )
        elif isinstance(node, ast.Assign):
            # Record module-level assignments as ``[assignment]`` so a
            # rewrite that flips an ``assignment → def/class`` (e.g.
            # ``Foo = type("Foo", (), {})`` → ``def Foo(): pass``) shows
            # up as a snapshot diff. Without this entry the surface
            # helper keeps ``Foo`` in the public set unchanged and the
            # signatures dict sees ``Foo`` as a NEW symbol, missing the
            # kind flip. The reverse direction (``def`` → assignment)
            # was already covered by the line-1128 fallback before this
            # change; with this entry both directions now hit the
            # primary ``changed_set`` path.
            for target in node.targets:
                _record_assignment_target(target)
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            # Only annotated assignments with a bound value bind a
            # runtime module attribute; a bare ``PUBLIC_NAME: int``
            # declaration is a type hint, not an export. Mirrors the
            # corresponding branch in ``_snapshot_public_surface``.
            _record_assignment_target(node.target)
    return signatures


def _collect_python_public_surface(source: str) -> List[str]:
    """Backward-compatible wrapper for older tests and local imports."""
    return sorted(_snapshot_public_surface(source, "python"))


def _prompt_allows_breaking_change(prompt_content: Optional[str]) -> bool:
    """Backward-compatible wrapper for the public marker helper."""
    return _prompt_has_breaking_change_marker(prompt_content)


def _verify_public_surface_regression(
    existing_code: Optional[str],
    generated_code: str,
    prompt_name: str,
    output_path: Optional[str],
    language: Optional[str],
    prompt_content: Optional[str],
) -> None:
    """Fail when a mature Python module generation removes public symbols."""
    if (
        not existing_code
        or not existing_code.strip()
        or _env_flag_enabled("PDD_SKIP_PUBLIC_SURFACE_GATE")
        or _env_flag_enabled("PDD_SKIP_CONFORMANCE")
        or _is_test_output_path(output_path)
        or not _is_python_generation(language, output_path)
    ):
        return

    before = _snapshot_public_surface(existing_code, language or "python")
    after = _snapshot_public_surface(generated_code, language or "python")
    if not before:
        return
    allowed_removed = _prompt_breaking_change_removed_symbols(prompt_content)
    removed = [
        symbol
        for symbol in _diff_public_surface(before, after)
        if symbol not in allowed_removed
    ]
    before_signatures = _snapshot_public_signatures(existing_code, language or "python")
    after_signatures = _snapshot_public_signatures(generated_code, language or "python")
    allowed_signature_changes = _prompt_breaking_change_signature_symbols(prompt_content)
    changed_set = {
        symbol
        for symbol, signature in before_signatures.items()
        if (
            symbol in after_signatures
            and after_signatures[symbol] != signature
            and symbol not in allowed_signature_changes
        )
    }
    for symbol in before_signatures:
        if symbol in after_signatures or symbol in changed_set:
            continue
        if "." in symbol:
            continue
        if symbol in after and symbol not in allowed_signature_changes:
            changed_set.add(symbol)
    changed_signatures = sorted(changed_set)
    if removed or changed_signatures:
        raise PublicSurfaceRegressionError(
            prompt_name=prompt_name,
            output_path=output_path or "",
            removed_symbols=removed,
            changed_signatures=changed_signatures,
            pre_surface_size=len(before),
            post_surface_size=len(after),
        )


def _get_test_churn_threshold() -> float:
    """Return the PDD_TEST_CHURN_THRESHOLD as a clamped 0..1 ratio.

    Accepts either a decimal ratio (``"0.40"``) or a percent string
    (``"40%"`` / ``"100%"``). The percent suffix is stripped and the value
    is divided by 100 before clamping. Unparseable values (``"invalid"``)
    log a warning and fall back to the documented default of ``0.40`` so
    a typo doesn't silently disable the gate.
    """
    raw = os.environ.get("PDD_TEST_CHURN_THRESHOLD", "0.40")
    text = (raw or "").strip()
    if not text:
        return 0.40
    is_percent = text.endswith("%")
    if is_percent:
        text = text[:-1].rstrip()
    try:
        value = float(text)
    except (TypeError, ValueError):
        logger.warning(
            "PDD_TEST_CHURN_THRESHOLD=%r is not a number; "
            "falling back to default 0.40.",
            raw,
        )
        return 0.40
    if is_percent:
        value /= 100.0
    if value < 0:
        return 0.0
    if value > 1:
        return 1.0
    return value


def _compute_test_churn_ratio(pre_text: str, post_text: str) -> float:
    before_lines = (pre_text or "").splitlines()
    after_lines = (post_text or "").splitlines()
    diff = difflib.unified_diff(before_lines, after_lines, lineterm="")
    added = 0
    removed = 0
    for line in diff:
        if line.startswith(("+++", "---", "@@")):
            continue
        if line.startswith("+"):
            added += 1
        elif line.startswith("-"):
            removed += 1
    if removed == 0:
        return 0.0
    return min(max(added, removed) / max(len(before_lines), 1), 1.0)


def _calculate_test_churn_ratio(before: str, after: str) -> float:
    """Backward-compatible wrapper for the prompt-named churn helper."""
    return _compute_test_churn_ratio(before, after)


def _verify_test_churn(
    existing_code: Optional[str],
    generated_code: str,
    prompt_name: str,
    output_path: Optional[str],
    prompt_content: Optional[str],
) -> None:
    """Fail when rewriting an existing test file exceeds the churn threshold."""
    if (
        not existing_code
        or not existing_code.strip()
        or _env_flag_enabled("PDD_SKIP_TEST_CHURN_GATE")
        or _env_flag_enabled("PDD_SKIP_CONFORMANCE")
        or not _is_test_output_path(output_path)
        or _prompt_allows_test_churn(prompt_content)
    ):
        return

    threshold = _get_test_churn_threshold()
    ratio = _compute_test_churn_ratio(existing_code, generated_code)
    if ratio > threshold:
        raise TestChurnError(
            prompt_name=prompt_name,
            output_path=output_path or "",
            churn_ratio=ratio,
            threshold=threshold,
            pre_line_count=len(existing_code.splitlines()),
            post_line_count=len(generated_code.splitlines()),
        )

def _should_wire_generated_exports(output_path: str) -> bool:
    """Return True when generated Python exports should be wired to __init__.py.

    Wiring mutates a sibling file, so the safe default is off. Users can opt in
    with PDD_ENABLE_WIRING=1; PDD_SKIP_WIRING remains a backward-compatible
    override for automation that already relies on it.
    """
    if not str(output_path).endswith('.py'):
        return False
    if _env_flag_enabled("PDD_SKIP_WIRING"):
        return False
    return _env_flag_enabled("PDD_ENABLE_WIRING")


def _find_prompt_contract_project_root(prompt_path: str, output_path: Optional[str]) -> pathlib.Path:
    """Find the project root used for prompt contract preflight resolution."""
    starts: List[pathlib.Path] = []
    try:
        starts.append(pathlib.Path(prompt_path).resolve().parent)
    except Exception:
        pass
    if output_path:
        try:
            starts.append(pathlib.Path(output_path).resolve().parent)
        except Exception:
            pass
    starts.append(pathlib.Path.cwd().resolve())

    seen: set[pathlib.Path] = set()
    for start in starts:
        if start in seen:
            continue
        seen.add(start)
        current = start
        while True:
            if (current / "architecture.json").exists():
                return current
            if current.parent == current:
                break
            current = current.parent

    try:
        current = pathlib.Path(prompt_path).resolve().parent
        while True:
            if current.name == "prompts":
                return current.parent
            if current.parent == current:
                break
            current = current.parent
    except Exception:
        pass

    return pathlib.Path.cwd().resolve()

# --- Git Helper Functions ---
def _run_git_command(command: List[str], cwd: Optional[str] = None) -> Tuple[int, str, str]:
    """Runs a git command and returns (return_code, stdout, stderr)."""
    try:
        process = subprocess.run(command, capture_output=True, text=True, check=False, cwd=cwd, encoding='utf-8')
        return process.returncode, process.stdout.strip(), process.stderr.strip()
    except FileNotFoundError:
        return -1, "", "Git command not found. Ensure git is installed and in your PATH."
    except Exception as e:
        return -2, "", f"Error running git command {' '.join(command)}: {e}"

def is_git_repository(path: Optional[str] = None) -> bool:
    """Checks if the given path (or current dir) is a git repository."""
    start_path = pathlib.Path(path).resolve() if path else pathlib.Path.cwd()
    # Check for .git in current or any parent directory
    current_path = start_path
    while True:
        if (current_path / ".git").is_dir():
            # Verify it's the root of the work tree or inside it
            returncode, stdout, _ = _run_git_command(["git", "rev-parse", "--is-inside-work-tree"], cwd=str(start_path))
            return returncode == 0 and stdout == "true"
        parent = current_path.parent
        if parent == current_path: # Reached root directory
            break
        current_path = parent
    return False


def _expand_vars(text: str, vars_map: Optional[Dict[str, str]]) -> str:
    """Replace $KEY and ${KEY} in text when KEY exists in vars_map. Leave others unchanged."""
    if not text or not vars_map:
        return text

    def repl_braced(m: re.Match) -> str:
        key = m.group(1)
        return vars_map.get(key, m.group(0))

    def repl_simple(m: re.Match) -> str:
        key = m.group(1)
        return vars_map.get(key, m.group(0))

    # Replace ${KEY} first, then $KEY
    text = re.sub(r"\$\{([A-Za-z_][A-Za-z0-9_]*)\}", repl_braced, text)
    text = re.sub(r"\$([A-Za-z_][A-Za-z0-9_]*)", repl_simple, text)
    return text


def _parse_front_matter(text: str) -> Tuple[Optional[Dict[str, Any]], str]:
    """Parse YAML front matter at the start of a prompt and return (meta, body).

    Accepts LF, CRLF, or mixed line endings and a leading UTF-8 BOM (#1276) —
    Windows editors frequently save prompts with CRLF and/or BOM, either of
    which the previous string-prefix check rejected. Trailing whitespace on
    the fence lines is tolerated to match ``template_registry._parse_front_matter``.

    Only the malformed-YAML path is logged — that condition requires BOTH
    fences to be present, so it is unambiguous user intent. The unclosed-fence
    case is silent because ``---\\nProse...`` is also a valid markdown
    horizontal rule and we cannot distinguish "intended front matter, forgot
    to close" from "markdown HR" without false positives.
    """
    # Strip a leading UTF-8 BOM (U+FEFF) if present — Windows editors that
    # save as UTF-8-with-BOM would otherwise make the anchor fail silently.
    if text.startswith("﻿"):
        text = text[1:]
    m = re.match(r"^---[ \t]*\r?\n(.*?)\r?\n---[ \t]*(?:\r?\n|\Z)", text, re.DOTALL)
    if not m:
        return None, text
    fm_body = m.group(1)
    rest = text[m.end():]
    import yaml as _yaml
    try:
        meta = _yaml.safe_load(fm_body) or {}
    except _yaml.YAMLError as exc:
        logger.warning(
            "Failed to parse YAML front matter: %s. Treating entire prompt as body.",
            exc,
        )
        return None, text
    if not isinstance(meta, dict):
        meta = {}
    return meta, rest


def _is_architecture_template(meta: Optional[Dict[str, Any]]) -> bool:
    """Detect the packaged architecture JSON template via its front matter name."""
    return isinstance(meta, dict) and meta.get("name") == "architecture/architecture_json"


def _repair_architecture_interface_types(payload: Any) -> Tuple[Any, bool]:
    """
    Patch common LLM slip-ups for the architecture template where interface.type
    occasionally returns an unsupported value like "object". Only normalizes the
    interface.type field and leaves other schema issues untouched so validation
    still fails for genuinely malformed outputs.
    """
    allowed_types = {
        "component",
        "page",
        "module",
        "api",
        "graphql",
        "cli",
        "job",
        "message",
        "config",
    }
    changed = False
    if not isinstance(payload, list):
        return payload, changed

    for entry in payload:
        if not isinstance(entry, dict):
            continue
        interface = entry.get("interface")
        if not isinstance(interface, dict):
            continue
        raw_type = interface.get("type")
        normalized = raw_type.lower() if isinstance(raw_type, str) else None
        if normalized in allowed_types:
            if normalized != raw_type:
                interface["type"] = normalized
                changed = True
            continue

        inferred_type = None
        for key in ("page", "component", "module", "api", "graphql", "cli", "job", "message", "config"):
            if isinstance(interface.get(key), dict):
                inferred_type = key
                break
        if inferred_type is None:
            inferred_type = "module"

        if raw_type != inferred_type:
            interface["type"] = inferred_type
            changed = True

    return payload, changed


def _collect_python_symbols(body: List[ast.stmt], prefix: str) -> List[str]:
    """Recursively collect symbol names from a Python AST body.

    At the module level (``prefix=""``), returns top-level functions, classes,
    and module constants (``X = ...`` / ``X: T = ...``). Inside a class
    (``prefix="ClassName."``), returns ``ClassName.method`` for each
    direct-child method and ``ClassName.Inner`` / ``ClassName.Inner.method``
    for nested classes.

    Methods defined inside ``if``/``try``/``with`` branches inside a class
    body are deliberately NOT collected: conformance is a hard validator and
    must not accept a symbol whose existence at runtime depends on branch
    evaluation (``if False: def maybe(self): ...`` must not satisfy
    ``ClassName.maybe``).
    """
    symbols: List[str] = []
    for node in body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            symbols.append(f"{prefix}{node.name}")
        elif isinstance(node, ast.ClassDef):
            class_name = f"{prefix}{node.name}"
            symbols.append(class_name)
            symbols.extend(_collect_python_symbols(node.body, prefix=f"{class_name}."))
        elif not prefix and isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    symbols.append(target.id)
        elif (
            not prefix
            and isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and node.value is not None
        ):
            # Only ``X: T = value`` binds at runtime; bare ``X: T`` does not
            # create a module export, so it must not satisfy conformance.
            symbols.append(node.target.id)
    return symbols


def _parse_declared_param_names(signature: str) -> Optional[List[str]]:
    """Parse a ``(arg, arg2=default, ...)`` signature string into parameter names.

    Returns the ordered list of parameter names (positional-only, positional,
    keyword-only) — variadic ``*args``/``**kwargs`` are intentionally excluded
    because a variadic catch-all does not satisfy a contract that declares a
    specific named parameter (a caller passing ``sync_metadata=False`` expects
    the callee to have that name in its signature).

    Returns ``None`` if the signature is not a parseable paren-list (e.g. a
    class header like ``class Foo(BaseModel)``); the caller should skip the
    signature check in that case.
    """
    if not signature or not isinstance(signature, str):
        return None
    sig = signature.strip()
    # Real architecture entries sometimes use class headers as "signatures"
    # (e.g. ``class Order(BaseModel)``). Only treat strings that start with
    # ``(`` as parameter lists.
    if not sig.startswith("("):
        return None
    try:
        tree = ast.parse(f"def _f{sig}: pass")
    except SyntaxError:
        return None
    fn = tree.body[0]
    if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return None
    args = fn.args
    names: List[str] = []
    names.extend(a.arg for a in args.posonlyargs)
    names.extend(a.arg for a in args.args)
    names.extend(a.arg for a in args.kwonlyargs)
    return names


def _collect_actual_param_names(func_node: ast.AST) -> List[str]:
    """Return positional + keyword-only parameter names for a FunctionDef-like AST node.

    ``*args`` and ``**kwargs`` are deliberately excluded: a variadic catch-all
    does not satisfy a declared named parameter for conformance purposes.
    """
    if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return []
    args = func_node.args
    names: List[str] = []
    names.extend(a.arg for a in args.posonlyargs)
    names.extend(a.arg for a in args.args)
    names.extend(a.arg for a in args.kwonlyargs)
    return names


# ``ParamSpec`` carries the three pieces of a parameter the signature
# conformance check compares: parameter name, annotation source (or
# ``None``), and default source (or ``None``). Sources are kept as
# whitespace-stripped strings (via ``ast.unparse``) so equality compares
# the canonical form and not the original quoting.
ParamSpec = Tuple[str, Optional[str], Optional[str]]


def _ast_args_to_specs(args: ast.arguments) -> List[ParamSpec]:
    """Return ``(name, annotation, default)`` tuples for positional+keyword args.

    Defaults align to the END of ``posonlyargs + args``. Variadic
    ``*args``/``**kwargs`` are intentionally omitted (a catch-all does not
    satisfy a contract that declares a specific named parameter).
    """
    out: List[ParamSpec] = []
    positional = list(args.posonlyargs) + list(args.args)
    defaults = list(args.defaults)
    default_offset = len(positional) - len(defaults)
    for i, arg in enumerate(positional):
        annotation = ast.unparse(arg.annotation).strip() if arg.annotation else None
        idx = i - default_offset
        default = (
            ast.unparse(defaults[idx]).strip() if 0 <= idx < len(defaults) else None
        )
        out.append((arg.arg, annotation, default))
    for arg, default in zip(args.kwonlyargs, args.kw_defaults):
        annotation = ast.unparse(arg.annotation).strip() if arg.annotation else None
        default_src = ast.unparse(default).strip() if default is not None else None
        out.append((arg.arg, annotation, default_src))
    return out


def _parse_declared_param_specs(signature: str) -> Optional[List[ParamSpec]]:
    """Parse a ``(arg: T, arg2=default, ...)`` signature into ``ParamSpec`` tuples.

    Returns ``None`` for non-paren-list signatures (e.g. class headers) so
    the caller can skip the signature check, mirroring
    :func:`_parse_declared_param_names`.
    """
    if not signature or not isinstance(signature, str):
        return None
    sig = signature.strip()
    if not sig.startswith("("):
        return None
    try:
        tree = ast.parse(f"def _f{sig}: pass")
    except SyntaxError:
        return None
    fn = tree.body[0]
    if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return None
    return _ast_args_to_specs(fn.args)


def _collect_actual_param_specs(func_node: ast.AST) -> List[ParamSpec]:
    """Return ``(name, annotation, default)`` tuples from an AST function node."""
    if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return []
    return _ast_args_to_specs(func_node.args)


def _find_target_function(
    tree: ast.Module, name: str
) -> Optional[ast.AST]:
    """Locate a declared function in the generated code.

    Resolution rules:
    * Bare name ``foo``:
        1. module-level ``def foo`` / ``async def foo``;
        2. module-level ``class foo`` — returns its ``__init__`` method if any
           (covers the "class methods: only check ``__init__``" rule).
    * Dotted name ``Outer.method`` / ``Outer.Inner.method``: descend through
      nested ``ClassDef`` nodes by name, then match the final segment as a
      method ``def`` / ``async def`` inside the resolved class body. This
      covers prompts whose ``pdd-interface`` declares class methods directly
      (e.g. ``ContentSelector.select``).

    Returns ``None`` if no matching definition exists.
    """
    if not isinstance(tree, ast.Module):
        return None

    parts = name.split(".") if name else []
    if not parts or any(not p for p in parts):
        return None

    # Walk through class containers for every segment except the last.
    body: List[ast.stmt] = list(tree.body)
    for part in parts[:-1]:
        cls: Optional[ast.ClassDef] = None
        for node in body:
            if isinstance(node, ast.ClassDef) and node.name == part:
                cls = node
                break
        if cls is None:
            return None
        body = list(cls.body)

    last = parts[-1]

    # Look for a direct function/method match first.
    for node in body:
        if (
            isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.name == last
        ):
            return node

    # Bare-name fallback: a module-level class — return its ``__init__``.
    if len(parts) == 1:
        for node in body:
            if isinstance(node, ast.ClassDef) and node.name == last:
                for child in node.body:
                    if (
                        isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
                        and child.name == "__init__"
                    ):
                        return child
                # Class exists but has no __init__ — nothing to compare against.
                return None

    return None


def _extract_pdd_interface_signatures(
    prompt_content: Optional[str],
    prompt_name: str,
) -> Tuple[List[Tuple[str, List[ParamSpec]]], bool]:
    """Extract ``(name, [ParamSpec])`` tuples from a prompt's ``<pdd-interface>``.

    Each ``ParamSpec`` is ``(param_name, annotation_source, default_source)``
    where the source strings are ``ast.unparse``-normalized or ``None``. This
    lets the verifier check name presence (the original Issue #928 case) plus
    annotation/default drift in a single pass.

    Returns ``(declarations, parse_error_logged)``:
      - ``declarations``: list of ``(function_name, declared_param_specs)``.
        Functions whose signature is not a parseable paren-list (class headers,
        TypeScript signatures, etc.) are skipped — they're outside the scope
        of this check.
      - ``parse_error_logged``: ``True`` when malformed JSON was found and a
        warning was emitted; caller should skip the signature check.

    Returns ``([], False)`` when no ``<pdd-interface>`` block is present (the
    new check is silent in that case to preserve existing behavior).
    """
    declarations: List[Tuple[str, List[ParamSpec]]] = []
    if not prompt_content:
        return declarations, False

    # Reuse the canonical parser from architecture_sync (verified non-circular
    # at module import time).
    try:
        from .architecture_sync import parse_prompt_tags
    except ImportError:
        return declarations, False

    tags = parse_prompt_tags(prompt_content)
    parse_error = tags.get("interface_parse_error")
    if parse_error:
        logger.warning(
            "pdd-interface JSON parse error in %s: %s — skipping signature "
            "conformance check.",
            prompt_name,
            parse_error,
        )
        return declarations, True

    interface = tags.get("interface")
    if not isinstance(interface, dict):
        return declarations, False

    iface_type = interface.get("type", "")
    candidates: List[Dict[str, Any]] = []
    if iface_type == "module":
        module_spec = interface.get("module") or {}
        candidates.extend(module_spec.get("functions") or [])
    elif iface_type == "cli":
        cli_spec = interface.get("cli") or {}
        candidates.extend(cli_spec.get("commands") or [])
    elif iface_type == "command":
        # The "command" interface type comes in two shapes used in the repo
        # today: a single ``command: {name, ...}`` dict, or a multi-command
        # ``command: {commands: [...]}`` list. Most current command prompts
        # omit ``signature`` (description-only), so the loop below silently
        # skips them via the ``params is None`` check — same fall-through
        # behavior as a class-header signature. Prompts that do declare a
        # signature get the same param-name conformance treatment as cli/
        # module entries.
        command_spec = interface.get("command") or {}
        commands_list = command_spec.get("commands")
        if isinstance(commands_list, list):
            candidates.extend(commands_list)
        elif command_spec.get("name"):
            candidates.append(command_spec)
    # Other iface_types (page, component, api) don't carry callable signatures
    # we can check this way.

    for item in candidates:
        if not isinstance(item, dict):
            continue
        name = item.get("name")
        sig = item.get("signature")
        if not name or not isinstance(name, str):
            continue
        params = _parse_declared_param_specs(sig) if isinstance(sig, str) else None
        if params is None:
            # Non-paren signature (e.g. "class Foo(BaseModel)") — skip.
            continue
        declarations.append((name, params))
    return declarations, False


def _verify_pdd_interface_signatures(
    generated_code: str,
    prompt_content: Optional[str],
    prompt_name: str,
    output_path: Optional[str],
    architecture_entry: Dict[str, Any],
) -> None:
    """Check that param names declared in ``<pdd-interface>`` exist in the code.

    Operates ONLY on functions/commands whose signature is a parseable paren
    list. Variadic ``*args``/``**kwargs`` in generated code do NOT satisfy a
    declared named parameter (e.g. ``def f(**kwargs)`` does not satisfy a
    declared ``sync_metadata`` kwarg — callers pass it by name).

    Raises ``ArchitectureConformanceError`` listing the missing parameters as
    dotted ``funcname.paramname`` entries so the existing repair-loop
    machinery surfaces them. Silently returns when:
      - no ``<pdd-interface>`` block is present in the prompt;
      - the JSON inside the block is malformed (a warning is logged);
      - none of the declared functions exists at module top-level (the
        existing symbol-existence check owns that error).
    """
    declarations, parse_error_logged = _extract_pdd_interface_signatures(
        prompt_content, prompt_name
    )
    if parse_error_logged or not declarations:
        return

    try:
        tree = ast.parse(generated_code)
    except SyntaxError:
        return  # Can't parse — defer to existing checks/recovery paths.

    missing_params: List[str] = []
    missing_funcs: List[str] = []
    # Signature drift detection:
    # * Annotations are checked conservatively — only raise when BOTH sides
    #   specify the annotation and the canonical sources differ. Adding an
    #   annotation later (gradual typing) should not churn the gate.
    # * Defaults are checked strictly — defaults are runtime signature
    #   behavior, not static metadata. A prompt declaring
    #   ``sync_metadata=False`` advertises that callers may omit the kwarg;
    #   generated code lacking the default breaks those callers with
    #   ``TypeError`` at runtime, so a missing default raises drift even
    #   if the annotation is intact.
    drifted: List[Tuple[str, str, str, str, str]] = []  # (func, param, kind, declared, actual)
    declared_expected: List[str] = []
    found_in_code: List[str] = []

    for func_name, declared_specs in declarations:
        target = _find_target_function(tree, func_name)
        if target is None:
            # Function/method declared by the prompt but absent from the
            # generated code. The prompt is the source of truth even when
            # architecture.json has no matching entry, so surface this here.
            # When architecture.json *does* declare the same symbol, its
            # check runs first and raises before this point, so no
            # double-fire occurs.
            missing_funcs.append(func_name)
            declared_expected.append(func_name)
            continue
        actual_specs = _collect_actual_param_specs(target)
        actual_by_name = {spec[0]: spec for spec in actual_specs}
        for declared_name, declared_ann, declared_default in declared_specs:
            dotted = f"{func_name}.{declared_name}"
            declared_expected.append(dotted)
            if declared_name not in actual_by_name:
                missing_params.append(dotted)
                continue
            found_in_code.append(dotted)
            _, actual_ann, actual_default = actual_by_name[declared_name]
            if (
                declared_ann
                and actual_ann
                and declared_ann != actual_ann
            ):
                drifted.append(
                    (func_name, declared_name, "annotation", declared_ann, actual_ann)
                )
            if declared_default is not None:
                if actual_default is None:
                    # Prompt declared a default; generated code dropped it.
                    # Callers relying on the optional kwarg would now break.
                    drifted.append(
                        (
                            func_name,
                            declared_name,
                            "default",
                            declared_default,
                            "<no default>",
                        )
                    )
                elif declared_default != actual_default:
                    drifted.append(
                        (
                            func_name,
                            declared_name,
                            "default",
                            declared_default,
                            actual_default,
                        )
                    )

    if not missing_params and not missing_funcs and not drifted:
        return

    # Dedup drift-dotted entries: one parameter can hit both annotation and
    # default drift in the same call, but ``missing_symbols`` should list the
    # canonical dotted symbol once (the per-kind detail lives in the message
    # and directive, not in the symbol set).
    seen: set = set()
    drifted_dotted: List[str] = []
    for func, param, *_ in drifted:
        dotted = f"{func}.{param}"
        if dotted in seen:
            continue
        seen.add(dotted)
        drifted_dotted.append(dotted)
    missing: List[str] = missing_funcs + missing_params + drifted_dotted
    output_display = output_path or "<unknown>"
    # Emit each failure category in a distinct sentence so the subprocess
    # parser can route each to the correct repair directive. A bare dotted
    # name like ``ContentSelector.select`` under the parameter shape would
    # otherwise be misread as ``func.param`` (= "On ContentSelector, add
    # parameter select").
    message_parts: List[str] = [
        f"Architecture conformance error for {prompt_name}:"
    ]
    if missing_funcs:
        message_parts.append(
            "the prompt's <pdd-interface> declares function(s)/method(s) "
            f"missing from the generated code: {', '.join(missing_funcs)}."
        )
    if missing_params:
        message_parts.append(
            "the prompt's <pdd-interface> declares parameter(s) missing "
            f"from the generated code: {', '.join(missing_params)}."
        )
    if drifted:
        drift_summary = ", ".join(
            f"{func}.{param} ({kind}: declared `{decl}`, found `{actual}`)"
            for func, param, kind, decl, actual in drifted
        )
        message_parts.append(
            "the prompt's <pdd-interface> declares parameter(s) whose "
            "signature drifted in the generated code: "
            f"{drift_summary}."
        )
    message_parts.append(f"Output: {output_display}.")
    message = " ".join(message_parts)

    directive_lines: List[str] = [
        f"Architecture conformance error for {prompt_name}: "
        "the prompt's <pdd-interface> declares function(s)/parameter(s) "
        "that are missing from or differ from the generated code.",
    ]
    if missing_funcs:
        directive_lines.append(
            "- Add the following missing function(s)/method(s) declared in "
            f"the prompt: `{', '.join(missing_funcs)}`."
        )
    missing_by_func: Dict[str, List[str]] = {}
    for dotted in missing_params:
        # rpartition so dotted method names like "ContentSelector.select.mode"
        # group as ("ContentSelector.select", "mode") rather than
        # ("ContentSelector", "select.mode"). partition() at the first dot
        # would misattribute the param to the class instead of the method.
        func, _, param = dotted.rpartition(".")
        missing_by_func.setdefault(func, []).append(param)
    for func, params in missing_by_func.items():
        directive_lines.append(
            f"- On `{func}`, add the following missing parameter(s) to the "
            f"signature and corresponding code paths: `{', '.join(params)}`."
        )
    for func, param, kind, declared_src, actual_src in drifted:
        directive_lines.append(
            f"- On `{func}`, update parameter `{param}` so its {kind} "
            f"matches the prompt: declared `{declared_src}`, "
            f"found `{actual_src}`."
        )
    directive_lines.append("")
    directive_lines.append(
        "Do not remove the declared parameters from the prompt's "
        "<pdd-interface>. The prompt is the source of truth — update the "
        "generated code to match it."
    )

    raise ArchitectureConformanceError(
        prompt_name=prompt_name,
        output_path=output_path or "",
        architecture_entry=architecture_entry or {},
        expected_symbols=declared_expected,
        found_symbols=found_in_code,
        missing_symbols=missing,
        message=message,
        repair_directive="\n".join(directive_lines),
    )


def _verify_architecture_conformance(
    generated_code: str,
    prompt_name: str,
    arch_path: Optional[str],
    language: Optional[str],
    verbose: bool,
    output_path: Optional[str] = None,
    prompt_content: Optional[str] = None,
) -> None:
    """Check generated code exports against architecture.json interface declarations.

    Raises ``click.UsageError`` on hard mismatch (missing declared symbols or
    naming convention violations).  Silently returns when no architecture entry
    exists or when the interface section is absent.

    Additionally, when ``prompt_content`` is provided and contains a
    ``<pdd-interface>`` block, verifies that each declared function/command's
    declared parameter names exist in the generated code's function signature
    (Issue #928). This catches cases where the existing symbol-existence
    check passes but the generated code silently drops a declared kwarg
    (e.g. ``sync_metadata=False``). The prompt is the source of truth for
    the interface contract, so this check runs even when ``architecture.json``
    has no matching entry.
    """
    entry = _verify_architecture_json_conformance(
        generated_code=generated_code,
        prompt_name=prompt_name,
        arch_path=arch_path,
        language=language,
        output_path=output_path,
    )

    # Additionally enforce the prompt's <pdd-interface> signature contract.
    # This catches "missing kwarg" bugs (Issue #928) where the function exists
    # (so the symbol-existence check above passes) but a declared parameter
    # like ``sync_metadata=False`` is silently absent from the signature.
    # The prompt is source of truth for parameter names, so this fires even
    # if architecture.json has no matching entry.
    _verify_pdd_interface_signatures(
        generated_code=generated_code,
        prompt_content=prompt_content,
        prompt_name=prompt_name,
        output_path=output_path,
        architecture_entry=entry or {},
    )


def _verify_architecture_json_conformance(
    generated_code: str,
    prompt_name: str,
    arch_path: Optional[str],
    language: Optional[str],
    output_path: Optional[str],
) -> Optional[Dict[str, Any]]:
    """Pre-existing architecture.json symbol-existence + camelCase check.

    Extracted from :func:`_verify_architecture_conformance` so the new
    ``<pdd-interface>`` signature check (Issue #928) can run independently
    even when the architecture.json side returns early. Returns the matched
    architecture entry (or ``None``) so callers can forward it to the
    secondary check.
    """
    if not arch_path:
        arch_path = "architecture.json"
    arch_file = pathlib.Path(arch_path)
    if not arch_file.exists():
        return None

    try:
        arch_data = json.loads(arch_file.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None

    # Find the matching architecture entry
    entry: Optional[Dict[str, Any]] = None
    basename = pathlib.Path(prompt_name).stem  # e.g. "models_Python"
    for item in extract_modules(arch_data):
        item_filename = item.get("filename", "")
        if item_filename == prompt_name or pathlib.Path(item_filename).stem == basename:
            entry = item
            break

    if entry is None:
        return None

    interface = entry.get("interface")
    if not isinstance(interface, dict):
        return entry

    # Collect declared symbols from the interface
    declared_symbols: List[str] = []
    iface_type = interface.get("type", "")

    if iface_type == "module":
        module_spec = interface.get("module", {})
        for func in module_spec.get("functions", []):
            name = func.get("name")
            if name:
                declared_symbols.append(name)
    elif iface_type == "api":
        api_spec = interface.get("api", {})
        for ep in api_spec.get("endpoints", []):
            # For API modules we don't check symbol names by default
            pass
    elif iface_type == "page":
        # Pages typically export a default — skip symbol checking
        return entry
    elif iface_type == "component":
        comp_spec = interface.get("component", {})
        for prop in comp_spec.get("props", []):
            pass  # Props aren't exported symbols
        return entry

    if not declared_symbols:
        return entry

    # Extract actual exports from generated code
    actual_symbols: List[str] = []
    detected_lang = (language or "").lower()

    if detected_lang in ("python", "py") or prompt_name.endswith("_Python.prompt"):
        try:
            tree = ast.parse(generated_code)
            actual_symbols.extend(_collect_python_symbols(tree.body, prefix=""))
        except SyntaxError:
            return entry  # Can't parse — skip conformance
    elif detected_lang in ("typescript", "javascript", "ts", "js") or any(
        prompt_name.endswith(sfx) for sfx in ("_TypeScript.prompt", "_TypeScriptReact.prompt", "_JavaScript.prompt", "_JavaScriptReact.prompt")
    ):
        export_pattern = re.compile(
            r"export\s+(?:default\s+)?(?:function|const|class|let|var|type|interface|enum)\s+(\w+)"
        )
        actual_symbols = export_pattern.findall(generated_code)
    else:
        return entry  # Unsupported language

    # Compare declared vs actual
    missing = [s for s in declared_symbols if s not in actual_symbols]
    if missing:
        raise ArchitectureConformanceError(
            prompt_name=prompt_name,
            output_path=output_path or "",
            architecture_entry=entry or {},
            expected_symbols=declared_symbols,
            found_symbols=actual_symbols,
            missing_symbols=missing,
        )

    # Check naming convention: if architecture specifies snake_case but code has camelCase.
    # Dotted symbols (``ClassName.method``) are split on ``.`` so the camelCase
    # guard inspects the method segment, not only the class-name prefix.
    if detected_lang in ("python", "py") or prompt_name.endswith("_Python.prompt"):
        camel_pattern = re.compile(r"^[a-z]+[A-Z]")
        camel_exports: List[str] = []
        for s in actual_symbols:
            for part in s.split("."):
                if not part.startswith("_") and camel_pattern.match(part):
                    camel_exports.append(s)
                    break
        if camel_exports:
            camel_message = (
                f"Architecture conformance error for {prompt_name}: "
                f"Python code uses camelCase names ({', '.join(camel_exports[:5])}) "
                f"but Python convention requires snake_case. "
                f"Output: {output_path or '<unknown>'}. "
                f"Expected: {declared_symbols}. Found: {actual_symbols}."
            )
            raise ArchitectureConformanceError(
                prompt_name=prompt_name,
                output_path=output_path or "",
                architecture_entry=entry or {},
                expected_symbols=declared_symbols,
                found_symbols=actual_symbols,
                missing_symbols=camel_exports,
                message=camel_message,
            )

    return entry


def get_git_content_at_ref(file_path: str, git_ref: str = "HEAD") -> Optional[str]:
    """Gets the content of the file as it was at the specified git_ref."""
    abs_file_path = pathlib.Path(file_path).resolve()
    if not is_git_repository(str(abs_file_path.parent)):
        return None
    
    returncode_rev, git_root_str, stderr_rev = _run_git_command(["git", "rev-parse", "--show-toplevel"], cwd=str(abs_file_path.parent))
    if returncode_rev != 0:
        # console.print(f"[yellow]Git (rev-parse) warning for {file_path}: {stderr_rev}[/yellow]")
        return None
    
    git_root = pathlib.Path(git_root_str)
    try:
        relative_path = abs_file_path.relative_to(git_root)
    except ValueError:
        # console.print(f"[yellow]File {file_path} is not under git root {git_root}.[/yellow]")
        return None

    returncode, stdout, stderr = _run_git_command(["git", "show", f"{git_ref}:{relative_path.as_posix()}"], cwd=str(git_root))
    if returncode == 0:
        return stdout
    else:
        # File might not exist at that ref, or other git error.
        # if "does not exist" not in stderr and "exists on disk, but not in" not in stderr and console.is_terminal: # Be less noisy for common cases
        #     console.print(f"[yellow]Git (show) warning for {file_path} at {git_ref}: {stderr}[/yellow]")
        return None

def get_file_git_status(file_path: str) -> str:
    """Gets the git status of a single file (e.g., ' M', '??', 'A '). Empty if clean."""
    abs_file_path = pathlib.Path(file_path).resolve()
    if not is_git_repository(str(abs_file_path.parent)) or not abs_file_path.exists():
        return ""
    returncode, stdout, _ = _run_git_command(["git", "status", "--porcelain", str(abs_file_path)], cwd=str(abs_file_path.parent))
    if returncode == 0:
        # stdout might be " M path/to/file" or "?? path/to/file"
        # We only want the status codes part
        status_part = stdout.split(str(abs_file_path.name))[0].strip() if str(abs_file_path.name) in stdout else stdout.strip()
        return status_part
    return ""

def git_add_files(file_paths: List[str], verbose: bool = False) -> bool:
    """Stages the given files using 'git add'."""
    if not file_paths:
        return True
    
    # Resolve paths and ensure they are absolute for git command
    abs_paths = [str(pathlib.Path(fp).resolve()) for fp in file_paths]
    
    # Determine common parent directory to run git command from, or git root
    # For simplicity, assume they are in the same repo and run from one of their parents
    if not is_git_repository(str(pathlib.Path(abs_paths[0]).parent)):
        if verbose:
            console.print(f"[yellow]Cannot stage files: {abs_paths[0]} is not in a git repository.[/yellow]")
        return False
        
    returncode, _, stderr = _run_git_command(["git", "add"] + abs_paths, cwd=str(pathlib.Path(abs_paths[0]).parent))
    if returncode == 0:
        if verbose:
            console.print(f"Successfully staged: [cyan]{', '.join(abs_paths)}[/cyan]")
        return True
    else:
        console.print(f"[red]Error staging files with git:[/red] {stderr}")
        return False
# --- End Git Helper Functions ---

def _find_default_test_files(tests_dir: Optional[str], code_file_path: Optional[str]) -> List[str]:
    """Find default test files for a given code file in the tests directory."""
    if not tests_dir or not code_file_path:
        return []

    tests_path = pathlib.Path(tests_dir)
    code_path = pathlib.Path(code_file_path)

    if not tests_path.exists() or not tests_path.is_dir():
        return []

    code_stem = code_path.stem
    code_suffix = code_path.suffix

    # Look for files starting with test_{code_stem}
    # We look for test_{code_stem}*.{code_suffix}
    # e.g., hello.py -> test_hello.py, test_hello_1.py
    pattern = f"test_{glob.escape(code_stem)}*{glob.escape(code_suffix)}"
    found_files = list(tests_path.glob(pattern))

    return [str(p) for p in sorted(found_files)]


def _detect_wireable_exports(code: str, file_path: str) -> list[str]:
    """Extract public function/class names from generated Python code."""
    if not file_path.endswith('.py'):
        return []
    try:
        tree = ast.parse(code)
        exports: list[str] = []
        for node in ast.iter_child_nodes(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if not node.name.startswith('_'):
                    exports.append(node.name)
            elif isinstance(node, ast.ClassDef):
                if not node.name.startswith('_'):
                    exports.append(node.name)
        return exports
    except SyntaxError:
        return []


def _wire_to_parent_init(output_path: str, exports: list[str], verbose: bool = False) -> bool:
    """Add import line for generated module to parent __init__.py if it exists.

    If an import line for this module already exists, merge any missing exports
    into that line instead of skipping wiring.
    """
    output_p = pathlib.Path(output_path)
    init_path = output_p.parent / '__init__.py'
    if not init_path.exists():
        return False
    module_name = output_p.stem
    existing = init_path.read_text(encoding='utf-8')

    # Look for an existing "from .{module_name} import ..." line
    pattern = rf"^from \.{re.escape(module_name)} import (.+)$"
    match = re.search(pattern, existing, flags=re.MULTILINE)

    if match:
        # Parse existing names and merge with new exports
        existing_names = [
            name.strip()
            for name in match.group(1).split(",")
            if name.strip()
        ]
        updated = False
        for name in exports:
            if name not in existing_names:
                existing_names.append(name)
                updated = True

        if not updated:
            return False

        import_line = f"from .{module_name} import {', '.join(existing_names)}"
        new_content = (
            existing[: match.start()]
            + import_line
            + existing[match.end():]
        )
    else:
        import_line = f"from .{module_name} import {', '.join(exports)}"
        new_content = existing.rstrip() + '\n' + import_line + '\n'

    init_path.write_text(new_content, encoding='utf-8')
    if verbose:
        console.print(f"[info]Wired exports to {init_path}: {import_line}[/info]")
    return True


def code_generator_main(
    ctx: click.Context,
    prompt_file: str,
    output: Optional[str],
    original_prompt_file_path: Optional[str],
    force_incremental_flag: bool,
    env_vars: Optional[Dict[str, str]] = None,
    unit_test_file: Optional[str] = None,
    exclude_tests: bool = False,
    language: Optional[str] = None,
    output_from_config: bool = False,
) -> Tuple[str, bool, float, str]:
    """
    CLI wrapper for generating code from prompts. Handles full and incremental generation,
    local vs. cloud execution, and output.

    Args:
        ctx: Click context carrying CLI flags (strength, temperature, verbose, force, etc.).
        prompt_file: Path to the .prompt file to generate from.
        output: Resolved output path. ``None`` means no caller-supplied path; the
            front-matter ``output:`` (or .pddrc default) will be used instead.
        original_prompt_file_path: Optional pinned reference for incremental diff.
        force_incremental_flag: Force incremental generation when possible.
        env_vars: Extra environment variables for template expansion.
        unit_test_file: Optional unit test path used by the cloud generator.
        exclude_tests: Whether to skip tests in the cloud payload.
        language: Optional explicit target language override.
        output_from_config: ``True`` when ``output`` was derived from
            ``.pddrc`` (``generate_output_path``) rather than an explicit
            ``--output`` CLI flag. When ``True``, a front-matter ``output:``
            value (if present) takes precedence over the .pddrc default.
            When ``False`` (CLI flag), the explicit path always wins. This
            preserves the documented precedence: CLI > front-matter > .pddrc.
            Defaults to ``False`` so existing callers stay backward compatible.

    Returns:
        Tuple of (generated_code, was_incremental, total_cost, model_name).
    """
    cli_params = ctx.obj or {}
    is_local_execution_preferred = cli_params.get('local', False)
    strength = cli_params.get('strength', DEFAULT_STRENGTH)
    temperature = cli_params.get('temperature', 0.0)
    time_budget = cli_params.get('time', DEFAULT_TIME)
    verbose = cli_params.get('verbose', False)
    force_overwrite = cli_params.get('force', False)
    quiet = cli_params.get('quiet', False)

    generated_code_content: Optional[str] = None
    was_incremental_operation = False
    total_cost = 0.0
    model_name = "unknown"

    input_file_paths_dict: Dict[str, str] = {"prompt_file": prompt_file}
    if original_prompt_file_path:
        input_file_paths_dict["original_prompt_file"] = original_prompt_file_path
    
    command_options: Dict[str, Any] = {"output": output}
    if language:
        command_options["language"] = language

    try:
        # Read prompt content once to determine LLM state and for construct_paths
        with open(prompt_file, 'r', encoding='utf-8') as f:
            raw_prompt_content = f.read()
        
        # Phase-2 templates: parse front matter metadata
        fm_meta, body = _parse_front_matter(raw_prompt_content)
        if fm_meta:
            prompt_content = body
        else:
            prompt_content = raw_prompt_content
        
        # Determine LLM state early to avoid unnecessary overwrite prompts
        llm_enabled: bool = True
        env_llm_raw = None
        try:
            if env_vars and 'llm' in env_vars:
                env_llm_raw = str(env_vars.get('llm'))
            elif os.environ.get('llm') is not None:
                env_llm_raw = os.environ.get('llm')
            elif os.environ.get('LLM') is not None:
                env_llm_raw = os.environ.get('LLM')
        except Exception:
            env_llm_raw = None

        # Environment variables should override front matter
        if env_llm_raw is not None:
            llm_enabled = _parse_llm_bool(env_llm_raw)
        elif fm_meta and isinstance(fm_meta, dict) and 'llm' in fm_meta:
            llm_enabled = bool(fm_meta.get('llm', True))
        # else: keep default True
        
        # If LLM is disabled, we're only doing post-processing, so skip overwrite confirmation
        effective_force = force_overwrite or not llm_enabled
        
        resolved_config, input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths_dict,
            force=effective_force,
            quiet=quiet,
            command="generate",
            command_options=command_options,
            context_override=ctx.obj.get('context'),
            confirm_callback=cli_params.get('confirm_callback')
        )
        # Determine final output path: if user passed a directory, use resolved file path
        resolved_output = output_file_paths.get("output")
        if output is None:
            output_path = resolved_output
        else:
            try:
                is_dir_hint = output.endswith(os.path.sep) or output.endswith("/")
            except Exception:
                is_dir_hint = False
            if is_dir_hint or os.path.isdir(output):
                output_path = resolved_output
            else:
                output_path = output

        # --- Unit Test Inclusion Logic ---
        test_files_to_include: List[str] = []
        if unit_test_file:
            test_files_to_include.append(unit_test_file)
        elif not exclude_tests:
            # Try to find default test files
            tests_dir = resolved_config.get("tests_dir")
            found_tests = _find_default_test_files(tests_dir, output_path)
            if found_tests:
                if verbose:
                    console.print(f"[info]Found default test files: {', '.join(found_tests)}[/info]")
                test_files_to_include.extend(found_tests)
        
        if test_files_to_include:
            prompt_content += "\n\n<unit_test_content>\n"
            prompt_content += (
                "Study these test files carefully before generating code. "
                "Pay special attention to:\n"
                "- What specific types and data structures the assertions reveal "
                "(e.g., if a test asserts `x == (1.0, 2.0)`, the value is a tuple, not a dict)\n"
                "- What mock patterns show about the real interfaces being called "
                "(e.g., `mock_config.get_jwt_token.return_value` reveals the auth API)\n"
                "- What import paths are used for internal modules\n"
                "- What fixture setup reveals about expected data formats "
                "(e.g., DataFrame column names, namedtuple fields)\n\n"
                "The generated code must pass these tests, but also match the "
                "implementation patterns they imply.\n"
            )
            for tf in test_files_to_include:
                try:
                    with open(tf, 'r', encoding='utf-8') as f:
                        content = f.read()
                    prompt_content += f"\nFile: {pathlib.Path(tf).name}\n```python\n{content}\n```\n"
                except Exception as e:
                    console.print(f"[yellow]Warning: Could not read unit test file {tf}: {e}[/yellow]")
            prompt_content += "</unit_test_content>\n"
        # ---------------------------------

        # Architecture-conformance repair directive (set by retrying callers
        # such as agentic_sync_runner / sync_main when a prior generation
        # failed conformance). Append to the prompt so the model sees the
        # missing-export instruction on the next attempt. Without this, the
        # subprocess retry would be an identical generation request and the
        # repair loop would not actually repair anything (#866).
        repair_directive_env = os.environ.get("PDD_REPAIR_DIRECTIVE")
        if repair_directive_env and repair_directive_env.strip():
            prompt_content += (
                "\n\n<architecture_repair_directive>\n"
                f"{repair_directive_env.strip()}\n"
                "</architecture_repair_directive>\n"
            )

    except FileNotFoundError as e:
        console.print(f"[red]Error: Input file not found: {e.filename}[/red]")
        return "", False, 0.0, "error"
    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except Exception as e:
        console.print(f"[red]Error during path construction: {e}[/red]")
        return "", False, 0.0, "error"

    can_attempt_incremental = False
    existing_code_content: Optional[str] = None
    original_prompt_content_for_incremental: Optional[str] = None

    # Merge -e vars with front-matter defaults; validate required
    if env_vars is None:
        env_vars = {}
    explicit_env_keys = set(env_vars.keys())  # Track which vars came from explicit -e
    if fm_meta and isinstance(fm_meta.get("variables"), dict):
        for k, spec in (fm_meta["variables"].items()):
            if isinstance(spec, dict):
                if k not in env_vars and "default" in spec:
                    env_vars[k] = str(spec["default"])
            # if scalar default allowed, ignore for now
        missing = [k for k, spec in fm_meta["variables"].items() if isinstance(spec, dict) and spec.get("required") and k not in env_vars]
        if missing:
            console.print(f"[error]Missing required variables: {', '.join(missing)}")
            return "", False, 0.0, "error"

    # Execute optional discovery from front matter to populate env_vars without overriding explicit -e values
    def _run_discovery(discover_cfg: Dict[str, Any]) -> Dict[str, str]:
        results: Dict[str, str] = {}
        try:
            if not discover_cfg:
                return results
            enabled = discover_cfg.get("enabled", False)
            if not enabled:
                return results
            root = discover_cfg.get("root", ".")
            patterns = discover_cfg.get("patterns", []) or []
            exclude = discover_cfg.get("exclude", []) or []
            max_per = int(discover_cfg.get("max_per_pattern", 0) or 0)
            max_total = int(discover_cfg.get("max_total", 0) or 0)
            root_path = pathlib.Path(root).resolve()
            seen: List[str] = []
            def _match_one(patterns_list: List[str]) -> List[str]:
                matches: List[str] = []
                for pat in patterns_list:
                    globbed = list(root_path.rglob(pat))
                    for p in globbed:
                        if any(p.match(ex) for ex in exclude):
                            continue
                        sp = str(p.resolve())
                        if sp not in matches:
                            matches.append(sp)
                    if max_per and len(matches) >= max_per:
                        matches = matches[:max_per]
                        break
                return matches
            # If a mapping 'set' is provided, compute per-variable results
            set_map = discover_cfg.get("set") or {}
            if isinstance(set_map, dict) and set_map:
                for var_name, spec in set_map.items():
                    if var_name in env_vars:
                        continue  # don't override explicit -e
                    v_patterns = spec.get("patterns", []) if isinstance(spec, dict) else []
                    v_exclude = spec.get("exclude", []) if isinstance(spec, dict) else []
                    save_exclude = exclude
                    try:
                        if v_exclude:
                            exclude = v_exclude
                        matches = _match_one(v_patterns or patterns)
                    finally:
                        exclude = save_exclude
                    if matches:
                        results[var_name] = ",".join(matches)
                        seen.extend(matches)
            # Fallback: populate SCAN_FILES and SCAN metadata
            if not results:
                files = _match_one(patterns)
                if max_total and len(files) > max_total:
                    files = files[:max_total]
                if files:
                    results["SCAN_FILES"] = ",".join(files)
            # Always set root/patterns helpers
            if root:
                results.setdefault("SCAN_ROOT", str(root_path))
            if patterns:
                results.setdefault("SCAN_PATTERNS", ",".join(patterns))
        except Exception as e:
            if verbose and not quiet:
                console.print(f"[yellow]Discovery skipped due to error: {e}[/yellow]")
        return results

    if fm_meta and isinstance(fm_meta.get("discover"), dict):
        discovered = _run_discovery(fm_meta.get("discover") or {})
        for k, v in discovered.items():
            if k not in env_vars:
                env_vars[k] = v

    # Inject EXAMPLE_OUTPUT_PATH for templates that reference ${EXAMPLE_OUTPUT_PATH}.
    # Precedence: explicit -e > resolved_config['example_output_path'] (#687)
    # > resolved_config['examples_dir'] (the SSOT helper's value, covering
    # greenfield + legacy context/ projects, #616) > template front-matter default.
    if "EXAMPLE_OUTPUT_PATH" not in explicit_env_keys and resolved_config:
        eop = resolved_config.get("example_output_path")
        if eop:
            env_vars["EXAMPLE_OUTPUT_PATH"] = str(eop).rstrip("/\\")
        elif resolved_config.get("examples_dir"):
            env_vars["EXAMPLE_OUTPUT_PATH"] = str(resolved_config["examples_dir"]).rstrip("/\\")

    # Expand variables in output path if provided
    if output_path:
        output_path = _expand_vars(output_path, env_vars)

    # Honor front-matter output when no explicit --output CLI flag was passed.
    # Front-matter overrides .pddrc generate_output_path (config default) but
    # NOT an explicit CLI --output flag. Precedence: CLI > front-matter > .pddrc.
    if (output is None or output_from_config) and fm_meta and isinstance(fm_meta.get("output"), str):
        try:
            meta_out = _expand_vars(fm_meta["output"], env_vars)
            if meta_out:
                output_path = str(pathlib.Path(meta_out).resolve())
        except Exception as fm_output_err:
            # Resolving the front-matter `output:` failed (bad path,
            # permission error, broken expansion, etc.). Fall back to the
            # caller-supplied path, but warn loudly so users notice — silent
            # fallback writes code to the wrong location.
            if not quiet:
                console.print(
                    f"[yellow]Warning: Could not resolve front-matter output path "
                    f"'{fm_meta.get('output')}': {fm_output_err}. "
                    f"Falling back to default output path.[/yellow]"
                )

    # Honor front-matter language if provided (overrides detection for both local and cloud)
    if fm_meta and isinstance(fm_meta.get("language"), str) and fm_meta.get("language"):
        language = fm_meta.get("language")

    if (
        llm_enabled
        and output_path
        and not _env_flag_enabled("PDD_SKIP_PROMPT_CONTRACT_PREFLIGHT")
    ):
        contract_root = _find_prompt_contract_project_root(prompt_file, output_path)
        contract_arch_path = contract_root / "architecture.json"
        contract_errors = validate_prompt_contract_context(
            prompt_path=pathlib.Path(prompt_file),
            output_path=pathlib.Path(output_path),
            project_root=contract_root,
            architecture_path=contract_arch_path if contract_arch_path.exists() else None,
            prompt_content=prompt_content,
        )
        if contract_errors:
            raise click.UsageError(
                "Prompt contract preflight failed:\n- " + "\n- ".join(contract_errors)
            )

    if output_path and pathlib.Path(output_path).exists():
        try:
            existing_code_content = pathlib.Path(output_path).read_text(encoding="utf-8")
        except Exception as e:
            console.print(f"[yellow]Warning: Could not read existing output file {output_path}: {e}[/yellow]")
            existing_code_content = None

        # Treat empty/whitespace-only files as absent — no code to incrementally patch
        if existing_code_content is not None and not existing_code_content.strip():
            existing_code_content = None

        if existing_code_content is not None:
            if "original_prompt_file" in input_strings:
                original_prompt_content_for_incremental = input_strings["original_prompt_file"]
                can_attempt_incremental = True
                if verbose:
                    console.print(f"Using specified original prompt: [cyan]{original_prompt_file_path}[/cyan]")
            elif is_git_repository(str(pathlib.Path(prompt_file).parent)):
                # prompt_content is the current on-disk version
                head_prompt_content = get_git_content_at_ref(prompt_file, git_ref="HEAD")

                if head_prompt_content is not None:
                    # Compare on-disk content (prompt_content) with HEAD content
                    if prompt_content.strip() != head_prompt_content.strip():
                        # Uncommitted changes exist. Original is HEAD, new is on-disk.
                        original_prompt_content_for_incremental = head_prompt_content
                        can_attempt_incremental = True
                        if verbose:
                            console.print(f"On-disk [cyan]{prompt_file}[/cyan] has uncommitted changes. Using HEAD version as original prompt.")
                    else:
                        # On-disk is identical to HEAD. Search for a prior *different* version.
                        if verbose:
                            console.print(f"On-disk [cyan]{prompt_file}[/cyan] matches HEAD. Searching for a prior *different* version as original prompt.")

                        new_prompt_candidate = head_prompt_content # This is also prompt_content (on-disk)
                        found_different_prior = False
                        
                        git_root_path_obj: Optional[pathlib.Path] = None
                        prompt_file_rel_to_root_str: Optional[str] = None

                        try:
                            abs_prompt_file_path = pathlib.Path(prompt_file).resolve()
                            temp_git_root_rc, temp_git_root_str, temp_git_root_stderr = _run_git_command(
                                ["git", "rev-parse", "--show-toplevel"], 
                                cwd=str(abs_prompt_file_path.parent)
                            )
                            if temp_git_root_rc == 0:
                                git_root_path_obj = pathlib.Path(temp_git_root_str)
                                prompt_file_rel_to_root_str = abs_prompt_file_path.relative_to(git_root_path_obj).as_posix()
                            elif verbose:
                                console.print(f"[yellow]Git (rev-parse) failed for {prompt_file}: {temp_git_root_stderr}. Cannot search history for prior different version.[/yellow]")
                        
                        except ValueError: # If file is not under git root
                             if verbose:
                                console.print(f"[yellow]File {prompt_file} not under a detected git root. Cannot search history.[/yellow]")
                        except Exception as e_git_setup:
                            if verbose:
                                console.print(f"[yellow]Error setting up git info for {prompt_file}: {e_git_setup}. Cannot search history.[/yellow]")

                        if git_root_path_obj and prompt_file_rel_to_root_str:
                            MAX_COMMITS_TO_SEARCH = 10  # How far back to look
                            log_cmd = ["git", "log", f"--pretty=format:%H", f"-n{MAX_COMMITS_TO_SEARCH}", "--", prompt_file_rel_to_root_str]
                            
                            log_rc, log_stdout, log_stderr = _run_git_command(log_cmd, cwd=str(git_root_path_obj))

                            if log_rc == 0 and log_stdout.strip():
                                shas = log_stdout.strip().split('\\n')
                                if verbose:
                                     console.print(f"Found {len(shas)} commits for [cyan]{prompt_file_rel_to_root_str}[/cyan] in recent history (up to {MAX_COMMITS_TO_SEARCH}).")

                                if len(shas) > 1: # Need at least one commit before the one matching head_prompt_content
                                    for prior_sha in shas[1:]: # Iterate starting from the commit *before* HEAD's version of the file
                                        if verbose:
                                            console.print(f"  Checking commit {prior_sha[:7]} for content of [cyan]{prompt_file}[/cyan]...")
                                        
                                        # get_git_content_at_ref uses the original prompt_file path, 
                                        # which it resolves internally relative to the git root.
                                        prior_content = get_git_content_at_ref(prompt_file, prior_sha) 
                                        
                                        if prior_content is not None:
                                            if prior_content.strip() != new_prompt_candidate.strip():
                                                original_prompt_content_for_incremental = prior_content
                                                can_attempt_incremental = True
                                                found_different_prior = True
                                                if verbose:
                                                    console.print(f"    [green]Found prior different version at commit {prior_sha[:7]}. Using as original prompt.[/green]")
                                                break 
                                            elif verbose:
                                                 console.print(f"    Content at {prior_sha[:7]} is identical to current HEAD. Skipping.")
                                        elif verbose:
                                            console.print(f"    Could not retrieve content for [cyan]{prompt_file}[/cyan] at commit {prior_sha[:7]}.")
                                else: 
                                    if verbose:
                                        console.print(f"  File [cyan]{prompt_file_rel_to_root_str}[/cyan] has less than 2 versions in recent history at this path.")
                            elif verbose:
                                console.print(f"[yellow]Git (log) failed for {prompt_file_rel_to_root_str} or no history found: {log_stderr}[/yellow]")
                        
                        if not found_different_prior:
                            original_prompt_content_for_incremental = new_prompt_candidate 
                            can_attempt_incremental = True 
                            if verbose:
                                console.print(
                                    f"[yellow]Warning: Could not find a prior *different* version of {prompt_file} "
                                    f"within the last {MAX_COMMITS_TO_SEARCH if git_root_path_obj else 'N/A'} relevant commits. "
                                    f"Using current HEAD version as original (prompts will be identical).[/yellow]"
                                )
                else:
                    # File not in HEAD, cannot determine git-based original prompt.
                    if verbose:
                        console.print(f"[yellow]Warning: Could not find committed version of {prompt_file} in git (HEAD) for incremental generation.[/yellow]")
            
            if force_incremental_flag and existing_code_content:
                if not (original_prompt_content_for_incremental or "original_prompt_file" in input_strings): # Check if original prompt is actually available
                     console.print(
                        "[yellow]Warning: --incremental flag used, but original prompt could not be determined. "
                        "Falling back to full generation.[/yellow]"
                    )
                else:
                    can_attempt_incremental = True 
    
    if force_incremental_flag and (not output_path or not pathlib.Path(output_path).exists()):
        console.print(
            "[yellow]Warning: --incremental flag used, but output file does not exist or path not specified. "
            "Performing full generation.[/yellow]"
        )
        can_attempt_incremental = False

    try:
        # Resolve post-process script from env/CLI override, then front matter, then sensible default per template
        post_process_script: Optional[str] = None
        prompt_body_for_script: str = prompt_content
        
        if verbose:
            console.print(f"[blue]LLM enabled:[/blue] {llm_enabled}")
        try:
            post_process_script = None
            script_override = None
            if env_vars:
                script_override = env_vars.get('POST_PROCESS_PYTHON') or env_vars.get('post_process_python')
            if not script_override:
                script_override = os.environ.get('POST_PROCESS_PYTHON') or os.environ.get('post_process_python')
            if script_override and str(script_override).strip():
                expanded = _expand_vars(str(script_override), env_vars)
                pkg_dir = pathlib.Path(__file__).parent.resolve()
                repo_root = pathlib.Path.cwd().resolve()
                repo_pdd_dir = (repo_root / 'pdd').resolve()
                candidate = pathlib.Path(expanded)
                if not candidate.is_absolute():
                    # 1) As provided, relative to CWD
                    as_is = (repo_root / candidate)
                    # 2) Under repo pdd/
                    under_repo_pdd = (repo_pdd_dir / candidate.name) if not as_is.exists() else as_is
                    # 3) Under installed package dir
                    under_pkg = (pkg_dir / candidate.name) if not as_is.exists() and not under_repo_pdd.exists() else as_is
                    if as_is.exists():
                        candidate = as_is
                    elif under_repo_pdd.exists():
                        candidate = under_repo_pdd
                    elif under_pkg.exists():
                        candidate = under_pkg
                    else:
                        candidate = as_is  # will fail later with not found
                post_process_script = str(candidate.resolve())
            elif fm_meta and isinstance(fm_meta, dict):
                raw_script = fm_meta.get('post_process_python')
                if isinstance(raw_script, str) and raw_script.strip():
                    # Expand variables like $VAR and ${VAR}
                    expanded = _expand_vars(raw_script, env_vars)
                    pkg_dir = pathlib.Path(__file__).parent.resolve()
                    repo_root = pathlib.Path.cwd().resolve()
                    repo_pdd_dir = (repo_root / 'pdd').resolve()
                    candidate = pathlib.Path(expanded)
                    if not candidate.is_absolute():
                        as_is = (repo_root / candidate)
                        under_repo_pdd = (repo_pdd_dir / candidate.name) if not as_is.exists() else as_is
                        under_pkg = (pkg_dir / candidate.name) if not as_is.exists() and not under_repo_pdd.exists() else as_is
                        if as_is.exists():
                            candidate = as_is
                        elif under_repo_pdd.exists():
                            candidate = under_repo_pdd
                        elif under_pkg.exists():
                            candidate = under_pkg
                        else:
                            candidate = as_is
                    post_process_script = str(candidate.resolve())
            # Fallback default: for architecture template, use built-in render_mermaid.py
            if not post_process_script:
                try:
                    prompt_str = str(prompt_file)
                    looks_like_arch_template = (
                        (isinstance(prompt_file, str) and (
                            prompt_str.endswith("architecture/architecture_json.prompt") or
                            prompt_str.endswith("architecture/architecture_json") or
                            "architecture_json.prompt" in prompt_str or
                            "architecture/architecture_json" in prompt_str
                        ))
                    )
                    looks_like_arch_output = (
                        bool(output_path) and pathlib.Path(str(output_path)).name == 'architecture.json'
                    )
                    if looks_like_arch_template or looks_like_arch_output:
                        pkg_dir = pathlib.Path(__file__).parent
                        repo_pdd_dir = pathlib.Path.cwd() / 'pdd'
                        if (pkg_dir / 'render_mermaid.py').exists():
                            post_process_script = str((pkg_dir / 'render_mermaid.py').resolve())
                        elif (repo_pdd_dir / 'render_mermaid.py').exists():
                            post_process_script = str((repo_pdd_dir / 'render_mermaid.py').resolve())
                except Exception:
                    post_process_script = None
            if verbose:
                console.print(f"[blue]Post-process script resolved to:[/blue] {post_process_script if post_process_script else 'None'}")
        except Exception:
            post_process_script = None
        # If LLM is disabled but no post-process script is provided, surface a helpful error
        if not llm_enabled and not post_process_script:
            console.print("[red]Error: llm: false requires 'post_process_python' to be specified in front matter.[/red]")
            return "", was_incremental_operation, total_cost, "error"
        if llm_enabled and can_attempt_incremental and existing_code_content is not None and original_prompt_content_for_incremental is not None:
            if verbose:
                console.print(Panel("Attempting incremental code generation...", title="[blue]Mode[/blue]", expand=False))

            if is_git_repository(str(pathlib.Path(prompt_file).parent)):
                files_to_stage_for_rollback: List[str] = []
                paths_to_check = [pathlib.Path(prompt_file).resolve()]
                if output_path and pathlib.Path(output_path).exists():
                    paths_to_check.append(pathlib.Path(output_path).resolve())

                for p_to_check in paths_to_check:
                    if not p_to_check.exists(): continue
                    
                    is_untracked = get_file_git_status(str(p_to_check)).startswith("??")
                    # Check if different from HEAD or untracked
                    is_different_from_head_rc = 1 if is_untracked else _run_git_command(["git", "diff", "--quiet", "HEAD", "--", str(p_to_check)], cwd=str(p_to_check.parent))[0]
                    
                    if is_different_from_head_rc != 0: # Different from HEAD or untracked
                        files_to_stage_for_rollback.append(str(p_to_check))
                
                if files_to_stage_for_rollback:
                    git_add_files(files_to_stage_for_rollback, verbose=verbose)
            
            # Preprocess both prompts: expand includes, substitute vars, then double.
            # Snapshot user-intent include paths from the ORIGINAL prompt (and the
            # post-`_expand_vars` variants for `${VAR}`-derived paths) so pass 2 can
            # gate the unresolved-include warning on real intent — pass 2 cannot
            # otherwise distinguish a literal `<include>` example in an expanded
            # source file's docstring from a real failed include (#1354 codex pass-3).
            from .preprocess import compute_user_intent_paths as _cuip
            orig_intent = _cuip(original_prompt_content_for_incremental) | _cuip(_expand_vars(original_prompt_content_for_incremental, env_vars))
            orig_proc = pdd_preprocess(original_prompt_content_for_incremental, recursive=True, double_curly_brackets=False)
            orig_proc = _expand_vars(orig_proc, env_vars)
            orig_proc = pdd_preprocess(orig_proc, recursive=False, double_curly_brackets=True, _user_intent_paths=orig_intent)

            new_intent = _cuip(prompt_content) | _cuip(_expand_vars(prompt_content, env_vars))
            new_proc = pdd_preprocess(prompt_content, recursive=True, double_curly_brackets=False)
            new_proc = _expand_vars(new_proc, env_vars)
            new_proc = pdd_preprocess(new_proc, recursive=False, double_curly_brackets=True, _user_intent_paths=new_intent)

            generated_code_content, was_incremental_operation, total_cost, model_name = incremental_code_generator_func(
                original_prompt=orig_proc,
                new_prompt=new_proc,
                existing_code=existing_code_content,
                language=language,
                strength=strength,
                temperature=temperature,
                time=time_budget,
                force_incremental=force_incremental_flag,
                verbose=verbose,
                preprocess_prompt=False
            )

            # Safety net: if incremental returned identical code, fall back to full generation.
            # The root-cause check lives in incremental_code_generator itself; this is
            # defense-in-depth in case a caller passes a different generator function.
            if (was_incremental_operation
                    and generated_code_content is not None
                    and existing_code_content is not None
                    and generated_code_content == existing_code_content):
                was_incremental_operation = False
                if verbose:
                    console.print("[yellow]Incremental patch produced no changes. Falling back to full generation.[/yellow]")

            if not was_incremental_operation:
                if verbose:
                    console.print(Panel("Incremental generator suggested full regeneration. Falling back.", title="[yellow]Fallback[/yellow]", expand=False))
            elif verbose:
                console.print(Panel(f"Incremental update successful. Model: {model_name}, Cost: ${total_cost:.6f}", title="[green]Incremental Success[/green]", expand=False))

        if llm_enabled and not was_incremental_operation: # Full generation path
            if verbose:
                console.print(Panel("Performing full code generation...", title="[blue]Mode[/blue]", expand=False))
            
            cloud_only = _env_flag_enabled("PDD_CLOUD_ONLY") or _env_flag_enabled("PDD_NO_LOCAL_FALLBACK")
            current_execution_is_local = is_local_execution_preferred and not cloud_only
            
            # Cloud auth cannot succeed in headless worker environments (no JWT
            # cache, no interactive device flow). Skip directly to local execution
            # to avoid warning messages that cause LLM agent bailout (issue #596).
            if not current_execution_is_local and CloudConfig.is_running_in_cloud():
                current_execution_is_local = True

            if not current_execution_is_local:
                if verbose: console.print("Attempting cloud code generation...")
                # Expand includes, substitute vars, then double. Pre-compute
                # user-intent include paths from the ORIGINAL prompt + post-
                # `_expand_vars` variants so pass 2 can gate the unresolved-
                # include warning against real intent (see #1354 codex pass-3).
                from .preprocess import compute_user_intent_paths as _cuip
                _cloud_intent = _cuip(prompt_content) | _cuip(_expand_vars(prompt_content, env_vars))
                processed_prompt_for_cloud = pdd_preprocess(prompt_content, recursive=True, double_curly_brackets=False, exclude_keys=[])
                processed_prompt_for_cloud = _expand_vars(processed_prompt_for_cloud, env_vars)
                processed_prompt_for_cloud = pdd_preprocess(processed_prompt_for_cloud, recursive=False, double_curly_brackets=True, exclude_keys=[], _user_intent_paths=_cloud_intent)
                if verbose: console.print(Panel(Text(processed_prompt_for_cloud, overflow="fold"), title="[cyan]Preprocessed Prompt for Cloud[/cyan]", expand=False))

                # Extract and display pinned example ID if present in prompt
                pin_match = re.search(r'<pin>([^<]+)</pin>', processed_prompt_for_cloud)
                if pin_match and verbose:
                    pinned_example_id = pin_match.group(1).strip()
                    console.print(f"[cyan]Using pinned example:[/cyan] {pinned_example_id}")

                # Get JWT token via CloudConfig (handles both injected tokens and device flow)
                jwt_token = CloudConfig.get_jwt_token(verbose=verbose)

                if not jwt_token:
                    if cloud_only:
                        console.print("[red]Cloud authentication failed.[/red]")
                        raise click.UsageError("Cloud authentication failed")
                    console.print("[yellow]Cloud authentication failed. Falling back to local execution.[/yellow]")
                    current_execution_is_local = True

                if jwt_token and not current_execution_is_local:
                    payload = {"promptContent": processed_prompt_for_cloud, "searchInput": prompt_content, "language": language, "strength": strength, "temperature": temperature, "verbose": verbose}
                    headers = {"Authorization": f"Bearer {jwt_token}", "Content-Type": "application/json"}
                    cloud_url = CloudConfig.get_endpoint_url("generateCode")
                    try:
                        response = requests.post(cloud_url, json=payload, headers=headers, timeout=get_cloud_request_timeout())
                        response.raise_for_status()
                        
                        response_data = response.json()
                        generated_code_content = response_data.get("generatedCode")
                        total_cost = float(response_data.get("totalCost", 0.0))
                        model_name = response_data.get("modelName", "cloud_model")

                        # Extract example information from examplesUsed array (cloud returns this)
                        examples_used = response_data.get("examplesUsed", [])
                        if examples_used:
                            selected_example_id = examples_used[0].get("id")
                            selected_example_title = examples_used[0].get("title")
                        else:
                            selected_example_id = None
                            selected_example_title = None

                        # Strip markdown code fences if present (cloud API returns fenced JSON)
                        if generated_code_content and isinstance(language, str) and language.strip().lower() == "json":
                            cleaned = generated_code_content.strip()
                            if cleaned.startswith("```json"):
                                cleaned = cleaned[7:]
                            elif cleaned.startswith("```"):
                                cleaned = cleaned[3:]
                            if cleaned.endswith("```"):
                                cleaned = cleaned[:-3]
                            generated_code_content = cleaned.strip()
                        if not generated_code_content:
                            if cloud_only:
                                console.print("[red]Cloud execution returned no code.[/red]")
                                raise click.UsageError("Cloud execution returned no code")
                            console.print("[yellow]Cloud execution returned no code. Falling back to local.[/yellow]")
                            current_execution_is_local = True
                        elif verbose:
                             # Display example info if available
                             if selected_example_id:
                                 example_info = f" | Example: {selected_example_id}"
                                 if selected_example_title:
                                     example_info += f" ({selected_example_title})"
                                 console.print(Panel(f"Cloud generation successful. Model: {model_name}, Cost: ${total_cost:.6f}{example_info}", title="[green]Cloud Success[/green]", expand=False))
                             else:
                                 console.print(Panel(f"Cloud generation successful. Model: {model_name}, Cost: ${total_cost:.6f}", title="[green]Cloud Success[/green]", expand=False))
                    except requests.exceptions.Timeout:
                        if cloud_only:
                            console.print(f"[red]Cloud execution timed out ({get_cloud_timeout()}s).[/red]")
                            raise click.UsageError("Cloud execution timed out")
                        console.print(f"[yellow]Cloud execution timed out ({get_cloud_timeout()}s). Falling back to local.[/yellow]")
                        current_execution_is_local = True
                    except requests.exceptions.HTTPError as e:
                        status_code = e.response.status_code if e.response else 0
                        err_content = e.response.text[:200] if e.response else "No response content"

                        # Non-recoverable errors: do NOT fall back to local
                        if status_code == 402:  # Insufficient credits
                            try:
                                error_data = e.response.json()
                                current_balance = error_data.get("currentBalance", "unknown")
                                estimated_cost = error_data.get("estimatedCost", "unknown")
                                console.print(f"[red]Insufficient credits. Current balance: {current_balance}, estimated cost: {estimated_cost}[/red]")
                            except Exception:
                                console.print(f"[red]Insufficient credits: {err_content}[/red]")
                            raise click.UsageError("Insufficient credits for cloud code generation")
                        elif status_code == 401:  # Authentication error
                            console.print(f"[red]Authentication failed: {err_content}[/red]")
                            raise click.UsageError("Cloud authentication failed")
                        elif status_code == 403:  # Authorization error (not approved)
                            console.print(f"[red]Access denied: {err_content}[/red]")
                            raise click.UsageError("Access denied - user not approved")
                        elif status_code == 400:  # Validation error (e.g., empty prompt)
                            console.print(f"[red]Invalid request: {err_content}[/red]")
                            raise click.UsageError(f"Invalid request: {err_content}")
                        else:
                            # Recoverable errors (5xx, unexpected errors): fall back to local
                            if cloud_only:
                                console.print(f"[red]Cloud HTTP error ({status_code}): {err_content}[/red]")
                                raise click.UsageError(f"Cloud HTTP error ({status_code}): {err_content}")
                            console.print(f"[yellow]Cloud HTTP error ({status_code}): {err_content}. Falling back to local.[/yellow]")
                            current_execution_is_local = True
                    except requests.exceptions.RequestException as e:
                        if cloud_only:
                            console.print(f"[red]Cloud network error: {e}[/red]")
                            raise click.UsageError(f"Cloud network error: {e}")
                        console.print(f"[yellow]Cloud network error: {e}. Falling back to local.[/yellow]")
                        current_execution_is_local = True
                    except json.JSONDecodeError:
                        if cloud_only:
                            console.print("[red]Cloud returned invalid JSON.[/red]")
                            raise click.UsageError("Cloud returned invalid JSON")
                        console.print("[yellow]Cloud returned invalid JSON. Falling back to local.[/yellow]")
                        current_execution_is_local = True
            
            if current_execution_is_local:
                if verbose: console.print("Executing code generator locally...")
                # Expand includes, substitute vars, then double; pass to local
                # generator with preprocess_prompt=False. Pre-compute user-intent
                # include paths from the ORIGINAL prompt + post-`_expand_vars`
                # variants so pass 2 can gate the unresolved-include warning
                # against real intent (see #1354 codex pass-3).
                from .preprocess import compute_user_intent_paths as _cuip
                _local_intent = _cuip(prompt_content) | _cuip(_expand_vars(prompt_content, env_vars))
                local_prompt = pdd_preprocess(prompt_content, recursive=True, double_curly_brackets=False, exclude_keys=[])
                local_prompt = _expand_vars(local_prompt, env_vars)
                local_prompt = pdd_preprocess(local_prompt, recursive=False, double_curly_brackets=True, exclude_keys=[], _user_intent_paths=_local_intent)
                # Language already resolved (front matter overrides detection if present)
                gen_language = language
                
                # Extract output schema from front matter if available
                output_schema = fm_meta.get("output_schema") if fm_meta else None
                
                generated_code_content, total_cost, model_name = local_code_generator_func(
                    prompt=local_prompt,
                    language=gen_language,
                    strength=strength,
                    temperature=temperature,
                    time=time_budget,
                    verbose=verbose,
                    preprocess_prompt=False,
                    output_schema=output_schema,
                )
                was_incremental_operation = False
                if verbose:
                    console.print(Panel(f"Full generation successful. Model: {model_name}, Cost: ${total_cost:.6f}", title="[green]Local Success[/green]", expand=False))

        # Optional post-process Python hook (runs after LLM when enabled, or standalone when LLM is disabled)
        if post_process_script:
            try:
                python_executable = detect_host_python_executable()
                # Choose stdin for the script: LLM output if available and enabled, else prompt body
                stdin_payload = generated_code_content if (llm_enabled and generated_code_content is not None) else prompt_body_for_script
                env = os.environ.copy()
                env['PDD_LANGUAGE'] = str(language or '')
                env['PDD_OUTPUT_PATH'] = str(output_path or '')
                env['PDD_PROMPT_FILE'] = str(pathlib.Path(prompt_file).resolve())
                env['PDD_LLM'] = '1' if llm_enabled else '0'
                try:
                    env['PDD_ENV_VARS'] = json.dumps(env_vars or {})
                except Exception:
                    env['PDD_ENV_VARS'] = '{}'
                # If front matter provides args, run in argv mode with a temp input file
                fm_args = None
                try:
                    # Env/CLI override for args (comma-separated or JSON list)
                    raw_args_env = None
                    if env_vars:
                        raw_args_env = env_vars.get('POST_PROCESS_ARGS') or env_vars.get('post_process_args')
                    if not raw_args_env:
                        raw_args_env = os.environ.get('POST_PROCESS_ARGS') or os.environ.get('post_process_args')
                    if raw_args_env:
                        s = str(raw_args_env).strip()
                        parsed_list = None
                        if s.startswith('[') and s.endswith(']'):
                            try:
                                parsed = json.loads(s)
                                if isinstance(parsed, list):
                                    parsed_list = [str(a) for a in parsed]
                            except Exception:
                                parsed_list = None
                        if parsed_list is None:
                            if ',' in s:
                                parsed_list = [part.strip() for part in s.split(',') if part.strip()]
                            else:
                                parsed_list = [part for part in s.split() if part]
                        fm_args = parsed_list or None
                    if fm_args is None:
                        raw_args = fm_meta.get('post_process_args') if isinstance(fm_meta, dict) else None
                        if isinstance(raw_args, list):
                            fm_args = [str(a) for a in raw_args]
                except Exception:
                    fm_args = None
                proc = None
                temp_input_path = None
                try:
                    if fm_args is None:
                        # Provide sensible default args for architecture template with render_mermaid.py
                        try:
                            if post_process_script and pathlib.Path(post_process_script).name == 'render_mermaid.py':
                                if isinstance(prompt_file, str) and prompt_file.endswith('architecture/architecture_json.prompt'):
                                    fm_args = ["{INPUT_FILE}", "{APP_NAME}", "{OUTPUT_HTML}"]
                        except Exception:
                            pass
                    if fm_args:
                        # When LLM is disabled, use the existing output file instead of creating a temp file
                        if not llm_enabled and output_path and pathlib.Path(output_path).exists():
                            temp_input_path = str(pathlib.Path(output_path).resolve())
                            env['PDD_POSTPROCESS_INPUT_FILE'] = temp_input_path
                        else:
                            # Write payload to a temp file for scripts expecting a file path input.
                            # LLM output must not touch output_path until conformance gates pass.
                            suffix = '.json' if (isinstance(language, str) and str(language).lower().strip() == 'json') or (output_path and str(output_path).lower().endswith('.json')) else '.txt'
                            with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix=suffix, encoding='utf-8') as tf:
                                tf.write(stdin_payload or '')
                                temp_input_path = tf.name
                            env['PDD_POSTPROCESS_INPUT_FILE'] = temp_input_path
                        # Compute placeholder values
                        app_name_val = (env_vars or {}).get('APP_NAME') if env_vars else None
                        if not app_name_val:
                            app_name_val = 'System Architecture'
                        output_html_default = None
                        if output_path and str(output_path).lower().endswith('.json'):
                            output_html_default = str(pathlib.Path(output_path).with_name(f"{pathlib.Path(output_path).stem}_diagram.html").resolve())
                        placeholder_map = {
                            'INPUT_FILE': temp_input_path or '',
                            'OUTPUT': str(output_path or ''),
                            'PROMPT_FILE': str(pathlib.Path(prompt_file).resolve()),
                            'APP_NAME': str(app_name_val),
                            'OUTPUT_HTML': str(output_html_default or ''),
                        }
                        def _subst_arg(arg: str) -> str:
                            # First expand $VARS using existing helper, then {TOKENS}
                            expanded = _expand_vars(arg, env_vars)
                            for key, val in placeholder_map.items():
                                expanded = expanded.replace('{' + key + '}', val)
                            return expanded
                        args_list = [_subst_arg(a) for a in fm_args]
                        if verbose:
                            console.print(Panel(f"Post-process hook (argv)\nScript: {post_process_script}\nArgs: {args_list}", title="[blue]Post-process[/blue]", expand=False))
                        proc = subprocess.run(
                            [python_executable, post_process_script] + args_list,
                            text=True,
                            capture_output=True,
                            timeout=300,
                            cwd=str(pathlib.Path(post_process_script).parent),
                            env=env
                        )
                    else:
                        # Run the script with stdin payload, capture stdout as final content
                        if verbose:
                            console.print(Panel(f"Post-process hook (stdin)\nScript: {post_process_script}", title="[blue]Post-process[/blue]", expand=False))
                        proc = subprocess.run(
                            [python_executable, post_process_script],
                            input=stdin_payload or '',
                            text=True,
                            capture_output=True,
                            timeout=300,
                            cwd=str(pathlib.Path(post_process_script).parent),
                            env=env
                        )
                finally:
                    if temp_input_path:
                        try:
                            # Only delete temp files, not the actual output file when llm=false.
                            is_resolved_output = bool(
                                output_path
                                and temp_input_path == str(pathlib.Path(output_path).resolve())
                            )
                            if (
                                proc
                                and proc.returncode == 0
                                and llm_enabled
                                and generated_code_content is not None
                                and not is_resolved_output
                            ):
                                generated_code_content = pathlib.Path(temp_input_path).read_text(
                                    encoding="utf-8"
                                )
                            if not is_resolved_output:
                                os.unlink(temp_input_path)
                        except Exception:
                            pass
                if proc and proc.returncode == 0:
                    if verbose:
                        console.print(Panel(f"Post-process success (rc=0)\nstdout: {proc.stdout[:150]}\nstderr: {proc.stderr[:150]}", title="[green]Post-process[/green]", expand=False))
                    # Do not modify generated_code_content to preserve architecture.json
                else:
                    rc = getattr(proc, 'returncode', 'N/A')
                    err = getattr(proc, 'stderr', '')
                    console.print(f"[yellow]Post-process failed (rc={rc}). Stderr:\n{err[:500]}[/yellow]")
            except FileNotFoundError:
                console.print(f"[yellow]Post-process script not found: {post_process_script}. Skipping.[/yellow]")
            except subprocess.TimeoutExpired:
                console.print("[yellow]Post-process script timed out. Skipping.[/yellow]")
            except Exception as e:
                console.print(f"[yellow]Post-process script error: {e}. Skipping.[/yellow]")
        if generated_code_content is not None:
            # Optional output_schema JSON validation before writing (only when LLM ran)
            if llm_enabled:
                try:
                    if fm_meta and isinstance(fm_meta.get("output_schema"), dict):
                        is_json_output = False
                        if isinstance(language, str) and str(language).lower().strip() == "json":
                            is_json_output = True
                        elif output_path and str(output_path).lower().endswith(".json"):
                            is_json_output = True
                        if is_json_output:
                            # Check if the generated content is an error message from llm_invoke
                            if generated_code_content.strip().startswith("ERROR:"):
                                raise click.UsageError(f"LLM generation failed: {generated_code_content}")
                                
                            parsed = json.loads(generated_code_content)

                            # Fix common LLM mistake: unwrap arrays wrapped in objects
                            # LLMs often return {"items": [...]} or {"type": "array", "items": [...]}
                            # when the schema expects a plain array [...]
                            output_schema = fm_meta.get("output_schema", {})
                            if output_schema.get("type") == "array" and isinstance(parsed, dict):
                                # Check for common wrapper patterns
                                if "items" in parsed and isinstance(parsed["items"], list):
                                    parsed = parsed["items"]
                                    generated_code_content = json.dumps(parsed, indent=2)
                                elif "data" in parsed and isinstance(parsed["data"], list):
                                    parsed = parsed["data"]
                                    generated_code_content = json.dumps(parsed, indent=2)
                                elif "results" in parsed and isinstance(parsed["results"], list):
                                    parsed = parsed["results"]
                                    generated_code_content = json.dumps(parsed, indent=2)

                            if _is_architecture_template(fm_meta):
                                parsed, repaired = _repair_architecture_interface_types(parsed)
                                if repaired:
                                    generated_code_content = json.dumps(parsed, indent=2)
                                # Issue #617: filename mirrors filepath (directory structure preserved)
                                if isinstance(parsed, list):
                                    from pdd.architecture_sync import normalize_architecture_filenames
                                    normalize_architecture_filenames(parsed)
                                generated_code_content = json.dumps(parsed, indent=2)
                            try:
                                import jsonschema
                                jsonschema.validate(instance=parsed, schema=fm_meta.get("output_schema"))
                            except ModuleNotFoundError:
                                if verbose and not quiet:
                                    console.print("[yellow]jsonschema not installed; skipping schema validation.[/yellow]")
                            except Exception as ve:
                                raise click.UsageError(f"Generated JSON does not match output_schema: {ve}")
                except json.JSONDecodeError as jde:
                    raise click.UsageError(f"Generated output is not valid JSON: {jde}")

            # Architecture conformance check: verify generated code exports match
            # the interface declarations in architecture.json (hard failure on mismatch)
            if not _env_flag_enabled("PDD_SKIP_CONFORMANCE") and generated_code_content:
                try:
                    _verify_architecture_conformance(
                        generated_code=generated_code_content,
                        prompt_name=pathlib.Path(prompt_file).name,
                        arch_path=None,  # Uses default architecture.json
                        language=language,
                        verbose=verbose,
                        output_path=output_path,
                        prompt_content=prompt_content,
                    )
                except ArchitectureConformanceError as conform_err:
                    conform_err.total_cost = float(total_cost or 0.0)
                    conform_err.model_name = model_name or "unknown"
                    raise  # Re-raise conformance errors as hard failures
                except click.UsageError:
                    raise  # Re-raise conformance errors as hard failures
                except Exception as conform_err:
                    if verbose and not quiet:
                        console.print(f"[yellow]Warning: Architecture conformance check failed: {conform_err}[/yellow]")

            if (
                not _env_flag_enabled("PDD_SKIP_CONFORMANCE")
                and generated_code_content
                and existing_code_content is not None
            ):
                try:
                    prompt_name = pathlib.Path(prompt_file).name
                    _verify_public_surface_regression(
                        existing_code=existing_code_content,
                        generated_code=generated_code_content,
                        prompt_name=prompt_name,
                        output_path=output_path,
                        language=language,
                        prompt_content=prompt_content,
                    )
                    _verify_test_churn(
                        existing_code=existing_code_content,
                        generated_code=generated_code_content,
                        prompt_name=prompt_name,
                        output_path=output_path,
                        prompt_content=prompt_content,
                    )
                except (PublicSurfaceRegressionError, TestChurnError) as compat_err:
                    if output_path and existing_code_content is not None:
                        try:
                            pathlib.Path(output_path).write_text(
                                existing_code_content,
                                encoding="utf-8",
                            )
                        except Exception as restore_err:
                            if verbose and not quiet:
                                console.print(
                                    f"[yellow]Warning: Could not restore {output_path} "
                                    f"after compatibility gate failure: {restore_err}[/yellow]"
                                )
                    compat_err.total_cost = float(total_cost or 0.0)
                    compat_err.model_name = model_name or "unknown"
                    raise

            if output_path:
                p_output = pathlib.Path(output_path)
                p_output.parent.mkdir(parents=True, exist_ok=True)

                final_content = generated_code_content

                # Validate <include> tags in generated prompt files (Issue #225 PR #286)
                if p_output.suffix == '.prompt' or language == 'prompt':
                    validated_content, invalid_includes = validate_prompt_includes(
                        final_content,
                        base_dir=str(p_output.parent),
                        remove_invalid=False,
                    )
                    final_content = validated_content
                    if invalid_includes:
                        if verbose or not quiet:
                            console.print(
                                f"[yellow]Warning: Found {len(invalid_includes)} invalid <include> tag(s) "
                                f"referencing non-existent files. Replaced with comments.[/yellow]"
                            )
                            for inv_path in invalid_includes:
                                console.print(f"  [dim]- {inv_path}[/dim]")

                # Inject architecture metadata tags for .prompt files (reverse sync)
                if p_output.suffix == '.prompt':
                    try:
                        # Check if this prompt has an architecture entry
                        arch_entry = get_architecture_entry_for_prompt(p_output.name)

                        # Only inject tags if:
                        # 1. Architecture entry exists
                        # 2. Content doesn't already have PDD tags (preserve manual edits)
                        if arch_entry and not has_pdd_tags(final_content):
                            tags = generate_tags_from_architecture(arch_entry)
                            if tags:
                                # Prepend tags to the generated content
                                final_content = tags + '\n\n' + final_content
                                if verbose:
                                    console.print("[info]Injected architecture metadata tags from architecture.json[/info]")
                    except Exception as e:
                        # Don't fail generation if tag injection fails
                        if verbose:
                            console.print(f"[yellow]Warning: Could not inject architecture tags: {e}[/yellow]")

                p_output.write_text(final_content, encoding="utf-8")
                if verbose or not quiet:
                    console.print(f"Generated code saved to: [green]{p_output.resolve()}[/green]")
                # Post-write: optionally wire exports to parent __init__.py.
                if _should_wire_generated_exports(str(p_output)):
                    try:
                        wiring_exports = _detect_wireable_exports(final_content, str(p_output))
                        if wiring_exports:
                            wired = _wire_to_parent_init(str(p_output), wiring_exports, verbose=verbose)
                            if wired and verbose and not quiet:
                                console.print(f"[green]Auto-wired {len(wiring_exports)} export(s) to parent __init__.py[/green]")
                    except Exception as wire_err:
                        if verbose:
                            console.print(f"[yellow]Warning: Auto-wiring failed: {wire_err}[/yellow]")
                # Safety net: ensure architecture HTML is generated post-write if applicable
                try:
                    # Prefer resolved script if available; else default for architecture outputs
                    script_path2 = post_process_script
                    if not script_path2:
                        looks_like_arch_output2 = pathlib.Path(str(p_output)).name == 'architecture.json'
                        if looks_like_arch_output2:
                            pkg_dir2 = pathlib.Path(__file__).parent
                            repo_pdd_dir2 = pathlib.Path.cwd() / 'pdd'
                            if (pkg_dir2 / 'render_mermaid.py').exists():
                                script_path2 = str((pkg_dir2 / 'render_mermaid.py').resolve())
                            elif (repo_pdd_dir2 / 'render_mermaid.py').exists():
                                script_path2 = str((repo_pdd_dir2 / 'render_mermaid.py').resolve())
                    if script_path2 and pathlib.Path(script_path2).exists():
                        app_name2 = os.environ.get('APP_NAME') or (env_vars or {}).get('APP_NAME') or 'System Architecture'
                        out_html2 = os.environ.get('POST_PROCESS_OUTPUT') or str(p_output.with_name(f"{p_output.stem}_diagram.html").resolve())
                        html_missing = not pathlib.Path(out_html2).exists()
                        always_run_for_arch = pathlib.Path(str(p_output)).name == 'architecture.json'
                        if always_run_for_arch or html_missing:
                            try:
                                py_exec2 = detect_host_python_executable()
                            except Exception:
                                py_exec2 = sys.executable
                            if verbose:
                                console.print(Panel(f"Safety net post-process\nScript: {script_path2}\nArgs: {[str(p_output.resolve()), app_name2, out_html2]}", title="[blue]Post-process[/blue]", expand=False))
                            sp2 = subprocess.run([py_exec2, script_path2, str(p_output.resolve()), app_name2, out_html2],
                                                 capture_output=True, text=True, cwd=str(pathlib.Path(script_path2).parent))
                            if sp2.returncode == 0 and not quiet:
                                print(f"✅ Generated: {out_html2}")
                            elif verbose:
                                console.print(f"[yellow]Safety net failed (rc={sp2.returncode}). stderr:\n{sp2.stderr[:300]}[/yellow]")
                except Exception:
                    pass
                # Post-step now runs regardless of LLM value via the general post-process hook above.
            elif not quiet:
                # No destination resolved; surface the generated code directly to the console.
                console.print(Panel(Text(generated_code_content, overflow="fold"), title="[cyan]Generated Code[/cyan]", expand=False))
                console.print("[yellow]No output path resolved; skipping file write and stdout print.[/yellow]")
        else:
            # If LLM was disabled and post-process ran, that's a success (no error)
            if not llm_enabled and post_process_script:
                if verbose or not quiet:
                    console.print("[green]Post-process completed successfully (LLM was disabled).[/green]")
            else:
                console.print("[red]Error: Code generation failed. No code was produced.[/red]")
                return "", was_incremental_operation, total_cost, model_name or "error"

    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except Exception as e:
        if isinstance(e, click.UsageError):
            raise

        # For any other unexpected error, we should fail hard so the CLI exits non-zero
        # Log the detailed traceback first if verbose
        if verbose:
            import traceback
            console.print(traceback.format_exc())

        raise click.UsageError(f"An unexpected error occurred: {e}")
        
    return generated_code_content or "", was_incremental_operation, total_cost, model_name
