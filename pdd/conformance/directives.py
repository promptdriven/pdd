"""Shared ``BREAKING-CHANGE`` directive grammar and ``PDD_*`` flag helpers.

The opt-out vocabulary a prompt author uses to authorise a change a conformance
gate would otherwise block. Parses only; reaches no gate decisions. The
test-churn gate owns its own verb-object grammar.
"""

import os
import re
from typing import Iterator, List, Optional, Set


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

def _prompt_allows_breaking_change(prompt_content: Optional[str]) -> bool:
    """Backward-compatible wrapper for the public marker helper."""
    return _prompt_has_breaking_change_marker(prompt_content)
