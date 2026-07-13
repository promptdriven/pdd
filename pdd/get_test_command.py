# pdd/get_test_command.py
"""Get language-appropriate test commands.

This module provides functions to resolve the appropriate test command
for a given test file based on:
1. CSV run_test_command (if non-empty)
2. Smart detection via default_verify_cmd_for()
3. None (triggers agentic fallback)
"""
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Tuple
import csv
import json
import os
import re
import shlex
import stat

from .agentic_langtest import default_verify_cmd_for
from .get_language import get_language
from .get_run_command import shell_safe_substitute


# Upper bound on how many concrete patterns a single workspace glob may expand
# to via ``{a,b}`` brace alternation. Real workspace configs use a handful of
# alternatives; a manifest that expands past this bound is treated as
# pathological (untrusted brace-bomb) and membership is failed closed rather
# than materializing an exponential list. See ``_expand_braces``.
_MAX_BRACE_EXPANSION = 1024

# Upper bound on the number of ``/``-separated segments in a single workspace
# glob. Real globs have a handful; a manifest with thousands of segments (e.g.
# a wall of ``**`` components) is hostile and fails membership closed rather
# than driving the matcher into pathological cost. See
# ``_relative_matches_workspace_glob``.
_MAX_GLOB_SEGMENTS = 256

# Upper bound on the number of raw glob entries evaluated for a single package's
# membership. A declaration with more entries than this is treated as hostile
# and fails membership closed. Combined with ``_MAX_BRACE_EXPANSION`` (which is
# an *aggregate* budget shared across every glob in one membership check), this
# bounds total brace expansion regardless of how the manifest splits the work.
_MAX_RAW_GLOBS = 4096

# Upper bound on the size of a workspace-declaration file we will read/parse. A
# larger manifest is treated as hostile and contributes no globs. These caps are
# small on purpose: parsing a JSON/YAML array of N short entries materializes N
# Python objects *before* the ``_MAX_RAW_GLOBS`` count guard can run, so an
# under-cap-but-huge-cardinality manifest could otherwise peak at hundreds of MB
# and OOM a worker. Real manifests are tiny (a handful of workspace globs), so
# these bounds keep peak parse memory well under ~100 MB with generous headroom.
# ``pnpm-workspace.yaml`` gets the smaller cap because YAML parsing amplifies more
# per input byte and a real pnpm workspace file is only a few KB.
_MAX_MANIFEST_BYTES = 1 * 1024 * 1024
_MAX_PNPM_YAML_BYTES = 256 * 1024

# Upper bound on the length (chars) of a single raw glob string. Real globs are
# a few dozen characters; a much longer one is hostile. This bounds not just the
# result *count* of brace expansion but its total *bytes*: brace expansion copies
# a glob's prefix/suffix per option, so without a length cap a long-prefix glob
# with a few brace groups (still under the count budget) could multiply into
# gigabytes of strings. Capping the raw glob length keeps expansion bounded in
# both count and size.
_MAX_GLOB_LENGTH = 4096

# Upper bound on the *aggregate* dynamic-program cells the glob matcher may fill
# across one membership check. Each glob costs ``(path_depth+1) * (segments+1)``
# cells; the per-glob and per-declaration caps bound each factor, but their
# product across many globs (up to the brace budget) times a deep path could
# still be tens of millions of cells (seconds of CPU). This aggregate budget
# fails membership closed on such a crafted manifest. Real declarations use a
# handful of short globs against a shallow path — far under this bound.
_MAX_MATCH_CELLS = 2_000_000

# Upper bound on the *aggregate* characters the brace scanner may examine across
# one membership check. Brace expansion re-scans a pattern to locate the next
# alternation, and a deeply nested singleton (`{`×400 … `}`×400) makes each of
# up to ``_MAX_BRACE_EXPANSION`` worklist entries re-walk that long prefix — so a
# tiny (<1 KB) manifest glob can stay within the byte/count/segment budgets yet
# cost tens of seconds of pure scanning. Charging every scanned character against
# this shared budget bounds that work and fails membership closed. Real globs
# expand to a handful of short patterns — orders of magnitude under this bound.
_MAX_BRACE_SCAN_WORK = 8_000_000

# Extglob prefix characters: one of these immediately before ``(`` (``?(``/``*(``/
# ``+(``/``@(``/``!(``) opens a minimatch extglob. minimatch expands these but the
# direct matcher does not, so a *complete* extglob group fails membership closed.
_EXTGLOB_PREFIXES = "?*+@!"


def _has_complete_extglob(pattern: str) -> bool:
    """True when ``pattern`` contains a *complete* extglob group — an extglob prefix
    (``?*+@!``) immediately followed by ``(`` and later a matching ``)``.

    An *incomplete* marker (``foo?(bar`` with no ``)``) is NOT flagged: minimatch
    reads it as the supported ``?`` wildcard plus a literal ``(``, exactly as the
    direct matcher does, so rejecting it would needlessly refuse a legitimate glob.
    A single linear scan: once any ``X(`` marker is seen, the next ``)`` completes a
    group."""
    seen_marker = False
    prev = ""
    for ch in pattern:
        if ch == "(" and prev in _EXTGLOB_PREFIXES:
            seen_marker = True
        elif ch == ")" and seen_marker:
            return True
        prev = ch
    return False


def _has_complete_bracket_class(raw: str) -> bool:
    """True when ``raw`` contains a *closed, non-empty* ``[...]`` bracket class. Two
    kinds are NOT flagged because minimatch treats them literally, so rejecting them
    would needlessly refuse a legitimate dir name:

      * an *unmatched* ``[`` (no closing ``]``), e.g. ``foo[bar``; and
      * an *empty* class ``[]``, ``[!]``, ``[^]`` (no member before the closing
        ``]``), e.g. a dir literally named ``[]``.

    Per POSIX/minimatch, a ``]`` in the *first member position* (immediately after
    ``[`` or its ``!``/``^`` negation marker) is a literal member, not the close —
    so ``[]]``, ``[^]]``, ``[!]]`` ARE non-empty classes (their content is ``]``)
    and ARE flagged. Only a class with ``[^…]`` negation or POSIX ``[[:…:]]``
    semantics, which diverge from a literal match, needs fail-closed handling.

    Runs in a single left-to-right pass (each ``find`` advances monotonically), so a
    hostile glob of a million unmatched ``[`` cannot drive quadratic rescanning."""
    i, n = 0, len(raw)
    while i < n:
        if raw[i] != "[":
            i += 1
            continue
        j = i + 1
        if j < n and raw[j] in "!^":  # a leading negation marker is not a member
            j += 1
        # The character at ``j`` (even ``]``) is the first class member; a real
        # class needs a *closing* ``]`` somewhere after it. A single forward search
        # suffices — no ``]`` after ``j`` means none exists for any later ``[``.
        if j < n and raw.find("]", j + 1) != -1:
            return True
        return False
    return False


def _is_range_body(body: str) -> bool:
    """True when ``body`` (the content of a ``{...}``) is a real minimatch brace
    *range*: ``X..Y`` or ``X..Y..Z`` where the two endpoints are BOTH ASCII integers
    (optional leading ``-`` — a leading ``+`` is NOT a range) or BOTH single ASCII
    letters, and the optional step ``Z`` is an ASCII integer.

    Anything else is NOT a range — minimatch leaves it literal — so it is NOT
    flagged: multi-character endpoints (``foo..bar``), non-integer numeric-looking
    endpoints (``1.0..3.0``), plus-prefixed (``+1..+3``), non-ASCII/Unicode digits or
    letters, and empty endpoints (``..``)."""
    parts = body.split("..")
    if len(parts) not in (2, 3):
        return False

    def _is_ascii_int(text: str) -> bool:  # optional leading '-' only, ASCII digits
        digits = text[1:] if text[:1] == "-" else text
        return bool(digits) and digits.isascii() and digits.isdigit()

    def _is_ascii_alpha(text: str) -> bool:  # a single ASCII letter
        return len(text) == 1 and text.isascii() and text.isalpha()

    start, end = parts[0], parts[1]
    endpoints_ok = (_is_ascii_int(start) and _is_ascii_int(end)) or (
        _is_ascii_alpha(start) and _is_ascii_alpha(end))
    if not endpoints_ok:
        return False
    return len(parts) == 2 or _is_ascii_int(parts[2])


def _has_brace_range(raw: str) -> bool:
    """True when ``raw`` contains a real minimatch brace *range* — a ``{...}`` group
    whose body matches range grammar (see ``_is_range_body``): ``{1..3}``, ``{a..c}``,
    ``{01..03}``, ``{1..9..2}``. A comma-only expander emits these literally, so they
    fail closed.

    Not flagged: a ``..`` outside any brace (dir ``foo..bar``); a comma-alternation
    or multi-character body (``{foo..bar,baz}``, ``{foo..bar}``, ``{1.0..3.0}``);
    an opaque ``${1..3}``; or an unbalanced ``{foo..bar``. Only *leaf* groups (no
    nested ``{``) can be ranges — a range body holds no braces — so per-``}`` body
    inspection is limited to leaves, keeping the whole scan linear. A range nested
    inside an alternation (``{a,{1..3}}``) is still caught as the inner leaf."""
    # Each frame: [open_index, opaque, has_inner_brace]. A ``${...}`` (or any group
    # inside one) is opaque; its body is literal, never a range.
    stack: list = []
    prev = ""
    for i, ch in enumerate(raw):
        if ch == "{":
            opaque = prev == "$" or (bool(stack) and stack[-1][1])
            if stack:
                stack[-1][2] = True  # parent now has a nested brace → not a leaf
            stack.append([i, opaque, False])
        elif ch == "}" and stack:
            open_i, opaque, has_inner = stack.pop()
            if not opaque and not has_inner and _is_range_body(raw[open_i + 1:i]):
                return True
        prev = ch
    return False  # an unbalanced '{' left open never closes → literal, not a range


def _raw_glob_unsupported(raw: str) -> bool:
    """Return True when the *raw* (unexpanded) glob uses a construct that must be
    rejected *before* brace expansion, because expansion would mis-handle it:

      * ``\\`` — backslash escapes of brace metacharacters (the expander is not
        escape-aware; ``{foo\\,bar}`` is two options, not three).

    Construct checks that depend on how the concrete pattern actually reads — bracket
    classes and extglobs, which brace expansion can *create* (``{?,x}(foo)`` →
    ``?(foo)``) or *destroy* (``{[,x}]`` → ``[]``, ``x]``) across alternatives — are
    NOT done here; they run per expanded pattern in
    ``_concrete_pattern_unsupported``.
    """
    return "\\" in raw


_LEADING_PREFIX_RE = re.compile(r"^\.?/+")


def _strip_one_leading(pattern: str) -> str:
    """Apply npm's leading normalization exactly once: strip an optional leading
    ``.`` immediately followed by the entire leading run of ``/`` (the ``^\\.?/+``
    that ``@npmcli/map-workspaces`` uses). So ``./x``, ``.//x``, ``/x``, ``//x`` all
    become ``x``, while a prefix left OVER is significant — ``/./x`` normalizes to
    ``./x`` (needing a literal ``.`` segment) and ``././x`` keeps its second ``./`` —
    so neither collapses to ``x`` and falsely matches a plain ``x`` package."""
    return _LEADING_PREFIX_RE.sub("", pattern, count=1)


def _effective_leading(pattern: str) -> str:
    """Return ``pattern``'s effective leading form for classification (e.g. a ``#``
    comment), using the SAME one-pass normalization as matching. A residual leading
    ``/`` or ``./`` after that one pass is an absolute/dot-slash remainder that the
    matcher never matches, so it is reported as empty (not a comment)."""
    rest = _strip_one_leading(pattern)
    if rest.startswith("/") or rest.startswith("./"):
        return ""
    return rest


def _concrete_pattern_unsupported(pattern: str) -> bool:
    """Return True when a fully brace-*expanded* (concrete) pattern uses a minimatch
    construct this matcher does not implement with faithful parity, so the whole
    membership check must fail closed:

      * a *closed, non-empty* ``[...]`` bracket class — ``[^a]`` negates in minimatch
        but ``^`` is literal in ``fnmatch``; POSIX ``[[:alpha:]]`` is unsupported. An
        unmatched literal ``[`` or an empty ``[]``/``[!]``/``[^]`` is fine (both treat
        it literally) and is NOT rejected.
      * a brace *range* — ``..`` inside a non-comma, non-``$`` brace group
        (``{1..3}``, ``{a..c}``, ``{01..03}``, ``{1..9..2}``), which a comma-only
        expander emits literally. A literal ``..`` outside braces, inside a comma
        alternation, or inside an opaque ``${...}`` is fine and NOT rejected.
      * a *complete* extglob group (``?(…)``/``*(…)``/``+(…)``/``@(…)``/``!(…)`` with
        a matching ``)``), which minimatch expands but the direct matcher does not.
        An *incomplete* marker (``foo?(bar`` with no ``)``) is minimatch's ``?``
        wildcard plus a literal ``(`` — the direct matcher agrees — so it is NOT
        rejected.

    Bracket classes and extglobs cannot cross a ``/`` (a class/group is confined to
    one path segment), so they are checked PER ``/``-delimited segment — otherwise a
    ``[`` in one segment and a ``]`` in another (``foo[/bar]``, which minimatch reads
    literally) would be misread as a class. Brace ranges are checked on the whole
    pattern (a brace body may legitimately contain ``/``).

    (The astral ``?`` divergence is handled directly in ``_wildcard_segment_match``,
    which matches over UTF-16 code units, so nothing about astral characters is
    rejected here.)

    Failing closed only forgoes crossing a workspace boundary (the leaf still uses
    its nearest ``package.json``); it never adopts a foreign config. Real workspace
    globs use ``*``/``**``/``{,}`` — not these — so legitimate declarations are
    unaffected.
    """
    for segment in pattern.split("/"):
        if _has_complete_bracket_class(segment) or _has_complete_extglob(segment):
            return True
    return _has_brace_range(pattern)


def _read_manifest_text(path: Path, max_bytes: int = _MAX_MANIFEST_BYTES) -> Optional[str]:
    """Read ``path`` as UTF-8, or return ``None`` (so callers fail closed) if it is
    missing, not a regular file, larger than ``max_bytes``, unreadable, or not
    valid UTF-8.

    The file must resolve to a *regular* file: a manifest that is a symlink to a
    character device or FIFO (e.g. ``/dev/zero``) reports ``st_size == 0`` yet
    would stream forever, so a byte-capped read from a regular-file-only handle is
    required — ``st_size`` alone is not trusted."""
    try:
        st = path.stat()  # follows symlinks; the *target* must be a regular file
        if not stat.S_ISREG(st.st_mode):
            return None
        if st.st_size > max_bytes:
            return None
        with open(path, "rb") as handle:
            data = handle.read(max_bytes + 1)
        if len(data) > max_bytes:
            return None  # grew past the cap between stat and read
        return data.decode("utf-8")
    except (OSError, UnicodeError):
        return None


class _PatternBudgetError(Exception):
    """Raised when an untrusted workspace pattern exceeds a safety budget
    (brace expansion or segment count), so membership can fail closed."""


class _BraceBudgetError(_PatternBudgetError):
    """Raised when a brace pattern would expand past ``_MAX_BRACE_EXPANSION``."""


@dataclass
class TestCommand:
    """Bundles a test command string with its required working directory.

    cwd=None means the caller decides the working directory (backward compatible).
    cwd=Path(...) means the test runner config was found there and must be used as cwd.
    """
    __test__ = False  # Prevent pytest from collecting this as a test class
    command: str
    cwd: Optional[Path] = None


def _relative_matches_workspace_glob(rel_parts: Tuple[str, ...], pattern: str,
                                     cell_budget: Optional[list] = None,
                                     work_budget: Optional[list] = None,
                                     pre_normalized: bool = False,
                                     dot: bool = False) -> bool:
    """Match a package's path segments against a single workspace glob pattern.

    Supports the segment semantics workspace tools use: ``*`` matches exactly one
    path segment (with fnmatch inside the segment) and ``**`` matches zero or more
    segments. A trailing ``/*`` therefore matches direct children only, while
    ``**`` spans any depth.

    Matching is an iterative ``O(len(rel) * len(pattern))`` dynamic program (no
    recursion and no list slicing), so a hostile pattern with many ``**``
    segments cannot drive it into exponential backtracking or ``RecursionError``.
    The segment count is bounded *before* the pattern is split (a cheap
    ``count('/')`` check), and a pattern past ``_MAX_GLOB_SEGMENTS`` raises
    ``_PatternBudgetError`` so membership fails closed without materializing a
    huge segment list.

    Dot semantics follow npm/minimatch's default (``dot: false``): a wildcard
    segment (``*``/``**`` or an fnmatch pattern) does NOT match a path segment
    that begins with ``.`` unless the *pattern* segment also begins with ``.``.
    So ``packages/*`` does not match ``packages/.shadow``, but ``packages/.*``
    does.
    """
    # Cheap guard before allocating the split list (a "slash wall" attack).
    if pattern.count("/") > _MAX_GLOB_SEGMENTS:
        raise _PatternBudgetError
    # Apply npm's leading normalization exactly ONCE. A residual leading ``/`` or
    # ``./`` (e.g. ``/./packages/*`` → ``./packages/*``) is an absolute/dot-slash
    # remainder that does not match a relative package path — never collapse it to
    # ``packages/*`` and falsely prove membership. When ``pre_normalized`` is set the
    # caller has ALREADY applied the single leading strip to the RAW pattern before
    # brace expansion (npm normalizes once, before minimatch expands braces), so a
    # brace-GENERATED leading ``/`` (e.g. ``{/packages/*,other/*}`` → ``/packages/*``)
    # is anchored and MUST NOT be stripped again — only the residual-significant check
    # runs here.
    rest = pattern if pre_normalized else _strip_one_leading(pattern)
    if rest.startswith("/") or rest.startswith("./"):
        return False
    # Drop empty segments (from ``//`` or a trailing ``/``); every internal ``.``
    # segment is significant and kept.
    pat_parts = [p for p in rest.split("/") if p != ""]
    if len(pat_parts) > _MAX_GLOB_SEGMENTS:
        raise _PatternBudgetError
    rel = list(rel_parts)
    n, m = len(rel), len(pat_parts)
    # Fast reject: without ``**`` every pattern segment consumes exactly one path
    # segment, so mismatched counts can never match — skip the DP (and its per-cell
    # character work) entirely. This bounds a manifest of many wildcard-heavy globs
    # against a deep path.
    if "**" not in pat_parts and m != n:
        return False
    # Charge this match's DP-table size against a shared aggregate budget so that
    # many long globs against a deep path cannot sum to tens of millions of cells.
    if cell_budget is not None:
        cell_budget[0] -= (n + 1) * (m + 1)
        if cell_budget[0] < 0:
            raise _PatternBudgetError
    # Per-segment work budget (shared across the walk) charges the character-level
    # matching so that many long wildcard segments cannot burn CPU under the cell cap.
    work = work_budget if work_budget is not None else [_MAX_BRACE_SCAN_WORK]
    return _segments_dp_match(rel, pat_parts, work, dot=dot)


def _segments_dp_match(rel: list, pat_parts: list, work: list,
                       dot: bool = False) -> bool:
    """Iterative ``O(len(rel) * len(pat_parts))`` dynamic program matching path
    segments ``rel`` against glob segments ``pat_parts`` (``*``/literal per segment,
    ``**`` spanning any depth). UTF-16 units and dot-flags are computed ONCE per segment
    (not per DP cell), and per-unit character work is charged against ``work`` — so a
    deep path against many long wildcard segments cannot burn CPU.

    ``dot`` selects minimatch's dot policy. With ``dot=False`` (the default, used for
    positive membership and pattern-vs-pattern preprocessing) a wildcard segment does
    NOT match a leading-dot name unless the pattern segment also begins with ``.``. With
    ``dot=True`` (used for npm's final IGNORE/negation matching, which npm applies via
    ``glob``'s dot:true ignore set) a wildcard DOES match leading-dot names — so
    ``packages/*`` excludes ``packages/.shadow``."""
    n, m = len(rel), len(pat_parts)
    rel_units = [_utf16_units(r) for r in rel]
    rel_is_dot = [r.startswith(".") for r in rel]
    # A ``.`` or ``..`` path segment is special in minimatch: NO wildcard or globstar
    # matches it — only the IDENTICAL literal segment does. (Relevant when a raw pattern
    # STRING like ``packages/./x`` is matched as a path during npm's pruning.)
    rel_is_dotdir = [r in (".", "..") for r in rel]
    pat_units = [None if p == "**" else _utf16_units(p) for p in pat_parts]
    pat_is_dot = [p.startswith(".") for p in pat_parts]
    # dp[i][j] is True when rel[i:] matches pat_parts[j:].
    dp = [[False] * (m + 1) for _ in range(n + 1)]
    dp[n][m] = True
    # rel exhausted: only trailing ``**`` segments can still match (each empty).
    for j in range(m - 1, -1, -1):
        dp[n][j] = pat_parts[j] == "**" and dp[n][j + 1]
    for i in range(n - 1, -1, -1):
        for j in range(m - 1, -1, -1):
            if rel_is_dotdir[i]:
                # ``.``/``..`` matches ONLY an identical literal pattern segment.
                dp[i][j] = (pat_parts[j] == rel[i]) and dp[i + 1][j + 1]
            elif pat_parts[j] == "**":
                # ``**`` matches zero segments (advance pattern) or one-or-more
                # (consume rel[i], stay on the same ``**``). Under dot:false a
                # leading-dot segment is not consumed by ``**``.
                dp[i][j] = dp[i][j + 1] or (
                    (dot or not rel_is_dot[i]) and dp[i + 1][j])
            elif (not dot) and rel_is_dot[i] and not pat_is_dot[j]:
                # dot:false — a wildcard segment does not match a leading-dot name
                # unless the pattern segment also begins with ``.``.
                dp[i][j] = False
            else:
                dp[i][j] = (dp[i + 1][j + 1]
                            and _wildcard_units_match(rel_units[i], pat_units[j], work))
    return dp[0][0]


def _utf16_units(text: str) -> list:
    """Return ``text`` as a list of UTF-16 code units (ints). A non-BMP / astral
    character becomes its two-unit surrogate pair, matching how minimatch (a JS
    regex) counts characters — so a single ``?`` matches one unit and an emoji needs
    ``??``."""
    units: list = []
    for ch in text:
        code = ord(ch)
        if code > 0xFFFF:
            code -= 0x10000
            units.append(0xD800 + (code >> 10))
            units.append(0xDC00 + (code & 0x3FF))
        else:
            units.append(code)
    return units


def _wildcard_units_match(name_u: list, pat_u: list,
                          work: Optional[list] = None) -> bool:
    """Match one path segment against one glob segment, both given as UTF-16 code-unit
    lists, in the matcher's *own* supported language — literal units plus ``*`` (any
    run, including empty) and ``?`` (exactly one unit) — and NOTHING else.

    Working over UTF-16 units gives ``?`` exact minimatch parity even for astral
    characters (``?`` matches one surrogate unit; an emoji needs ``??``). Every other
    character, including ``[ ] ( ) { } ^ ! $`` and ``.``, is a literal — this
    deliberately does NOT delegate to ``fnmatch``, whose ``[...]``/``[^…]``
    reinterpretation and OS case-folding diverge from minimatch on the literal
    bracket forms this matcher intentionally permits (e.g. a dir named ``[^]``).

    Linear-space greedy two-pointer with single-star backtracking. Each unit examined
    is charged against the ``work`` budget (shared across the discovery walk), so a
    manifest of many long wildcard segments cannot burn CPU under the DP-cell cap."""
    if work is None:
        work = [_MAX_BRACE_SCAN_WORK]
    q, star = 0x3F, 0x2A  # ord('?'), ord('*') — always wildcards in a glob
    s = p = 0
    star_p = star_s = -1
    ns, npat = len(name_u), len(pat_u)
    while s < ns:
        work[0] -= 1
        if work[0] < 0:
            raise _PatternBudgetError
        if p < npat and pat_u[p] == star:
            # A pattern ``*`` is ALWAYS a wildcard — test it BEFORE literal equality, or
            # a literal ``*`` in the NAME (e.g. the pattern-string ``packages/**`` used as
            # a "path" during npm's pattern-vs-pattern pruning) would be consumed as a
            # literal match and ``**`` would fail to match the glob ``*``.
            star_p, star_s = p, s
            p += 1
        elif p < npat and (pat_u[p] == q or pat_u[p] == name_u[s]):
            s += 1
            p += 1
        elif star_p != -1:
            p = star_p + 1
            star_s += 1
            s = star_s
        else:
            return False
    while p < npat and pat_u[p] == star:
        work[0] -= 1  # charge trailing-star runs too (a long ``*``-wall is unbounded here)
        if work[0] < 0:
            raise _PatternBudgetError
        p += 1
    return p == npat


def _wildcard_segment_match(name: str, pat: str) -> bool:
    """Convenience wrapper: match segment strings by converting to UTF-16 units. See
    :func:`_wildcard_units_match`."""
    return _wildcard_units_match(_utf16_units(name), _utf16_units(pat))


def _workspace_source_is_pnpm(ancestor: Path) -> bool:
    """True when ``ancestor`` declares its workspace via ``pnpm-workspace.yaml`` (even
    a dangling symlink). pnpm's ``@pnpm/matcher`` evaluates include/exclude in
    DECLARATION ORDER (last matching pattern wins — a later positive re-includes),
    whereas npm/yarn's ``@npmcli/map-workspaces`` and lerna glob the positives and
    remove the negatives as a set (an exclusion is terminal; a later broad positive
    does NOT re-include). See ``_package_matches_workspace``'s ``ordered`` argument."""
    pnpm_path = ancestor / "pnpm-workspace.yaml"
    return pnpm_path.exists() or pnpm_path.is_symlink()


def _workspace_globs_for(ancestor: Path, cache: Optional[dict] = None) -> list:
    """Return the workspace package globs declared by ``ancestor`` (empty if none).

    Reads npm/yarn ``workspaces`` (list or ``{"packages": [...]}``), ``lerna.json``
    ``packages``, and ``pnpm-workspace.yaml`` ``packages``.

    ``pnpm-workspace.yaml``, when present, is *authoritative*: pnpm ignores the
    ``workspaces`` field in ``package.json``, so a stale or attacker-controlled
    ``workspaces`` list must not union in and broaden membership beyond what pnpm
    itself would honor. pnpm requires a YAML parser; if it is unavailable or the
    file cannot be parsed we conservatively return no globs so membership stays
    unproven rather than falsely asserted.

    Every source is validated to be the expected JSON/YAML shape (a mapping);
    a manifest whose top level is a non-object (e.g. ``[]``) contributes no
    globs instead of raising. Each declared package glob must be a genuine
    ``str`` — a list containing a non-string entry (e.g. ``[true]``, which would
    otherwise coerce to the glob ``"True"``) is treated as malformed and
    contributes no globs (fail closed).

    Results are memoized in ``cache`` (keyed by the canonical ancestor path) for
    the duration of one discovery walk so an ancestor manifest is parsed at most
    once even when the walk revisits it via ``_workspace_root_for``.
    """
    if cache is not None:
        try:
            key = os.path.realpath(str(ancestor))
        except (OSError, RuntimeError):
            key = str(ancestor)
        if key in cache:
            return cache[key]
        result = _workspace_globs_uncached(ancestor)
        cache[key] = result
        return result
    return _workspace_globs_uncached(ancestor)


_PNPM_YAML_LOADER_CACHE: dict = {}


def _pnpm_yaml_loader(yaml):
    """Return (memoized) a ``yaml.SafeLoader`` subclass whose scalar resolution and
    duplicate-key handling match pnpm's YAML 1.2 parser, so a ``pnpm-workspace.yaml``
    cannot prove/deny membership through a version discrepancy with PyYAML's default
    YAML 1.1 rules.

    The inherited YAML 1.1 implicit-resolver table is REPLACED wholesale with the
    YAML 1.2 *core schema* — layering selected rules onto the 1.1 table would still
    misclassify the forms 1.1 resolves but 1.2 does not: `yes`/`no`/`on`/`off` (1.1
    bool → 1.2 str), `0b10` (1.1 binary → 1.2 str), `1:20` (1.1 sexagesimal → 1.2
    str), `2020-01-01` (1.1 timestamp → 1.2 str), and `1_000` (1.1 underscore int →
    1.2 str), which pnpm treats as valid string globs. Under the 1.2 core schema only
    `true`/`false` (bool), `null`/`~`/empty (null), `[-+]?[0-9]+`/`0o…`/`0x…` (int),
    and the exponent/`.inf`/`.nan` floats resolve as non-strings; everything else —
    including ordinary globs and a quoted ``"0o12"`` — stays a string. A non-string
    ``packages`` entry is then rejected by ``_string_globs`` exactly as pnpm rejects
    a bare number/bool.

    pnpm also rejects duplicate mapping keys (PyYAML silently keeps the last); a
    custom map constructor raises on a duplicate so the parse fails closed.
    """
    cached = _PNPM_YAML_LOADER_CACHE.get("loader")
    if cached is not None:
        return cached

    class _Loader(yaml.SafeLoader):  # pylint: disable=too-few-public-methods
        pass

    _Loader.yaml_implicit_resolvers = {}  # drop PyYAML's inherited YAML 1.1 table
    _Loader.add_implicit_resolver(
        "tag:yaml.org,2002:bool",
        re.compile(r"^(?:true|True|TRUE|false|False|FALSE)$"), list("tTfF"))
    # Null includes the EMPTY scalar (``- `` with nothing after it) — YAML 1.2
    # resolves it to null, a non-string that must fail closed. PyYAML looks up the
    # empty-string first-char bucket, so register ``""`` and let the regex match "".
    _Loader.add_implicit_resolver(
        "tag:yaml.org,2002:null",
        re.compile(r"^(?:~|null|Null|NULL|)$"), ["~", "n", "N", ""])
    _Loader.add_implicit_resolver(
        "tag:yaml.org,2002:int",
        re.compile(r"^(?:[-+]?[0-9]+|0o[0-7]+|0x[0-9a-fA-F]+)$"),
        list("-+0123456789"))
    _Loader.add_implicit_resolver(
        "tag:yaml.org,2002:float",
        re.compile(
            r"^(?:[-+]?(?:\.[0-9]+|[0-9]+(?:\.[0-9]*)?)(?:[eE][-+]?[0-9]+)?"
            r"|[-+]?\.(?:inf|Inf|INF)|\.(?:nan|NaN|NAN))$"),
        list("-+0123456789."))

    def _construct_int_yaml_1_2(loader, node):
        # YAML 1.2 constructs an ordinary digit run as BASE 10 (``012`` is 12, not
        # octal 10 as YAML 1.1 does) and only ``0o``/``0x`` as bases 8/16. Getting
        # this right is what makes duplicate keys such as ``012:`` and ``12:``
        # (both integer 12 in 1.2) compare equal below.
        text = loader.construct_scalar(node)
        sign = -1 if text[:1] == "-" else 1
        digits = text[1:] if text[:1] in "+-" else text
        if digits[:2] == "0o":
            return sign * int(digits[2:], 8)
        if digits[:2] == "0x":
            return sign * int(digits[2:], 16)
        return sign * int(digits, 10)

    _Loader.add_constructor("tag:yaml.org,2002:int", _construct_int_yaml_1_2)

    def _construct_mapping_no_duplicates(loader, node, deep=False):
        mapping = {}
        for key_node, value_node in node.value:
            key = loader.construct_object(key_node, deep=deep)
            # Compare on (YAML tag, canonical value) so ``012``/``12`` (both int 12)
            # collide while a string ``"12"`` and int ``12`` stay distinct.
            marker = (key_node.tag, key)
            if marker in mapping:
                raise yaml.constructor.ConstructorError(
                    None, None, f"duplicate key {key!r}", key_node.start_mark)
            mapping[marker] = loader.construct_object(value_node, deep=deep)
        # Re-key by the plain constructed key so downstream ``data.get("packages")``
        # still works.
        return {marker[1]: value for marker, value in mapping.items()}

    _Loader.add_constructor(
        "tag:yaml.org,2002:map", _construct_mapping_no_duplicates)
    _PNPM_YAML_LOADER_CACHE["loader"] = _Loader
    return _Loader


def _workspace_globs_uncached(ancestor: Path) -> list:
    """See :func:`_workspace_globs_for`; this performs the actual filesystem read."""
    # ``pnpm-workspace.yaml`` is authoritative when *present at all* — even as a
    # dangling or unreadable symlink. ``Path.exists()`` returns False for a
    # dangling symlink, so use lexical presence; a present-but-unreadable pnpm
    # config yields no globs (fail closed) and must NOT fall through to a stale
    # ``package.json`` ``workspaces`` field.
    pnpm_path = ancestor / "pnpm-workspace.yaml"
    if pnpm_path.exists() or pnpm_path.is_symlink():
        try:
            import yaml  # optional dependency
        except ImportError:
            return []  # cannot parse pnpm config → membership unproven (fail closed)
        text = _read_manifest_text(pnpm_path, _MAX_PNPM_YAML_BYTES)  # None if missing/dangling/oversized/bad-utf8
        if text is None:
            return []
        try:
            # Parse with pnpm-compatible (YAML 1.2 core + no-duplicate-key) rules so
            # a version discrepancy cannot falsely prove membership.
            data = yaml.load(text, Loader=_pnpm_yaml_loader(yaml))
        except (yaml.YAMLError, ValueError, TypeError, RecursionError, OverflowError):
            # Any construction failure on untrusted YAML → membership unproven
            # (fail closed). ``yaml.YAMLError`` does NOT cover errors raised by
            # scalar constructors: e.g. a malformed timestamp such as
            # ``2020-99-99`` makes PyYAML raise a bare ``ValueError``
            # ("month must be in 1..12"), and huge integers can raise
            # ``OverflowError`` — none of which are ``yaml.YAMLError`` subclasses.
            return []
        if isinstance(data, dict):
            return _string_globs(data.get("packages"))
        return []

    globs: list = []
    manifest_path = ancestor / "package.json"
    if manifest_path.exists():
        text = _read_manifest_text(manifest_path)
        try:
            manifest = json.loads(
                text, parse_constant=_reject_json_constant) if text is not None else {}
        except (ValueError, RecursionError):
            # Malformed or deeply-nested (recursion-bomb) JSON → membership
            # unproven (fail closed) rather than crashing discovery.
            manifest = {}
        if isinstance(manifest, dict):
            ws = manifest.get("workspaces")
            if isinstance(ws, dict):
                ws = ws.get("packages")
            globs.extend(_string_globs(ws))
    lerna_path = ancestor / "lerna.json"
    if lerna_path.exists():
        text = _read_manifest_text(lerna_path)
        try:
            lerna = json.loads(
                text, parse_constant=_reject_json_constant) if text is not None else None
        except (ValueError, RecursionError):
            lerna = None  # parse failed → contribute nothing (fail closed)
        if isinstance(lerna, dict):
            if "packages" not in lerna:
                # Only an *omitted* ``packages`` key gets the documented lerna
                # default. A parse failure above sets ``lerna=None`` and skips
                # this, and an explicit ``"packages": null`` is NOT an omission —
                # it falls through to ``_string_globs(None)`` → no globs (fail
                # closed), so a crafted null must not grant the default glob.
                globs.append("packages/*")
            else:
                globs.extend(_string_globs(lerna["packages"]))
    return globs


def _reject_json_constant(token: str):
    """``parse_constant`` callback for ``json.loads``: raise on the non-standard
    ``NaN``/``Infinity``/``-Infinity`` constants that Python accepts but strict JSON
    parsers (npm's, Node's ``JSON.parse``) reject. A manifest using them is invalid
    JSON and must fail closed, even when the token sits outside the workspace field —
    a whole-document parse failure is what npm produces."""
    raise ValueError(f"invalid JSON constant {token!r}")


def _string_globs(value) -> list:
    """Return ``value`` as a list of string globs, or ``[]`` if it is not a list
    of strings. A single non-string entry makes the whole declaration malformed
    (fail closed) so a JSON/YAML ``true``/number cannot be coerced into a glob.

    A declaration with more than ``_MAX_RAW_GLOBS`` entries is rejected up front
    (before validating/copying the list) so a huge but under-byte-cap manifest
    fails membership closed without a second full-list traversal/copy."""
    if not isinstance(value, list):
        return []
    if len(value) > _MAX_RAW_GLOBS:
        return []
    if not all(isinstance(item, str) for item in value):
        return []
    return list(value)


def _split_top_level_commas(body: str, limit: int) -> list:
    """Split a brace body on commas that are not inside a nested brace group.

    Raises ``_BraceBudgetError`` once more than ``limit`` top-level options would
    be produced, so a brace body with millions of commas cannot materialize a
    huge list before the caller's budget is consulted.
    """
    parts, depth, current = [], 0, []
    for char in body:
        if char == "{":
            depth += 1
            current.append(char)
        elif char == "}":
            depth -= 1
            current.append(char)
        elif char == "," and depth == 0:
            parts.append("".join(current))
            current = []
            if len(parts) > limit:
                raise _BraceBudgetError
        else:
            current.append(char)
    parts.append("".join(current))
    if len(parts) > limit:
        raise _BraceBudgetError
    return parts


def _skip_balanced_braces(pattern: str, start: int, work: list) -> int:
    """Return the index just past the ``}`` matching the ``{`` at ``start`` (nesting
    included) when the group is *balanced*. When it is *unbalanced* (no matching
    ``}``), return ``start + 1`` so the caller treats only that one ``{`` as literal
    and keeps scanning — a later balanced alternation (e.g. the ``{a,b}`` in
    ``${foo/{a,b}``) must still expand. Each scanned character is charged against
    the ``work`` budget."""
    depth, i, n = 0, start, len(pattern)
    while i < n:
        work[0] -= 1
        if work[0] < 0:
            raise _BraceBudgetError
        if pattern[i] == "{":
            depth += 1
        elif pattern[i] == "}":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return start + 1  # unbalanced ${ → ``{`` is literal; resume after it


def _find_expandable_brace(pattern: str, limit: int,
                           work: Optional[list] = None) -> Optional[Tuple[int, int]]:
    """Return ``(start, end)`` of the first *expandable* ``{...}`` group — one whose
    body splits into two or more top-level options — or ``None`` when the pattern
    holds no real alternation.

    The scan runs left-to-right and, on hitting a *single-option* brace (``{foo}``,
    not a real alternation), does two things before giving up on it: it descends
    into that brace's body to find a nested alternation (so ``{a{b,c}}`` still
    expands its inner ``{b,c}``), and, failing that, it skips *past* the group and
    keeps scanning the rest of the pattern (so a later ``{a,b}`` in
    ``{foo}/{a,b}`` is still found). ``end`` indexes the matching ``}``.

    An *unmatched* opening ``{`` (no matching ``}``) is likewise literal and does
    not short-circuit the scan: only that one brace is skipped, so a later balanced
    alternation in ``{foo/{a,b}`` still expands. ``_split_top_level_commas`` may
    raise ``_BraceBudgetError`` for a comma bomb.

    Every character examined is charged against the mutable ``work`` budget (shared
    across the whole membership check). A deeply nested singleton makes this scan —
    and the descent below — re-walk a long prefix repeatedly; the budget raises
    ``_BraceBudgetError`` so such a pattern fails closed instead of burning CPU.
    """
    if work is None:
        work = [_MAX_BRACE_SCAN_WORK]
    i, n = 0, len(pattern)
    while i < n:
        # Charge every examined position — including the non-brace prefix skipped
        # below — so a long literal/``*`` run before the first brace (re-walked for
        # each of up to _MAX_BRACE_EXPANSION worklist entries) is bounded, not free.
        work[0] -= 1
        if work[0] < 0:
            raise _BraceBudgetError
        if pattern[i] != "{":
            i += 1
            continue
        depth, end = 0, -1
        for j in range(i, n):
            work[0] -= 1
            if work[0] < 0:
                raise _BraceBudgetError
            if pattern[j] == "{":
                depth += 1
            elif pattern[j] == "}":
                depth -= 1
                if depth == 0:
                    end = j
                    break
        if end == -1:
            i += 1  # unmatched '{' is literal; keep scanning for a later group
            continue
        body = pattern[i + 1:end]
        if len(_split_top_level_commas(body, limit)) >= 2:
            return (i, end)
        inner = _find_expandable_brace(body, limit, work)  # descend into singleton
        if inner is not None:
            return (i + 1 + inner[0], i + 1 + inner[1])
        i = end + 1  # fully literal group → skip past and keep scanning
    return None


_DOLLAR_MASK = "\x00"


def _mask_dollar_braces(pattern: str, work: list) -> Tuple[str, list]:
    """Replace every *balanced* ``${...}`` span (a ``{`` immediately preceded by a
    literal ``$``, nested braces included) with an inert ``\\x00N\\x00`` placeholder,
    returning the masked string and the list of removed literal spans.

    This is done BEFORE brace expansion so the expander never sees a ``$`` adjacent
    to a ``{``. Otherwise an option could generate that adjacency — expanding
    ``{$,x}{a,b}`` produces ``${a,b}``, whose ``{a,b}`` is NOT a shell group and MUST
    still expand — and a naive "``$`` precedes ``{``" opacity check on the worklist
    string would wrongly freeze it. An *unbalanced* ``${`` is left as a literal
    ``${`` (the later brace still expands). Each character is charged against
    ``work``."""
    literals: list = []
    out: list = []
    i, n = 0, len(pattern)
    while i < n:
        work[0] -= 1
        if work[0] < 0:
            raise _BraceBudgetError
        if pattern[i] == "$" and i + 1 < n and pattern[i + 1] == "{":
            end = _skip_balanced_braces(pattern, i + 1, work)
            if end > i + 2:  # a matching '}' was found → balanced ${...}
                out.append(f"{_DOLLAR_MASK}{len(literals)}{_DOLLAR_MASK}")
                literals.append(pattern[i:end])
                i = end
                continue
        out.append(pattern[i])
        i += 1
    return "".join(out), literals


def _restore_dollar_braces(pattern: str, literals: list) -> str:
    """Substitute ``\\x00N\\x00`` placeholders back with their original ``${...}``
    literal spans."""
    if not literals:
        return pattern
    return re.sub(
        rf"{_DOLLAR_MASK}(\d+){_DOLLAR_MASK}",
        lambda mo: literals[int(mo.group(1))],
        pattern,
    )


def _expand_braces(pattern: str, budget: Optional[list] = None,
                   work: Optional[list] = None) -> list:
    """Expand ``{a,b}`` brace alternations (as npm/Yarn workspace globs use) into
    concrete patterns. Unbalanced or single-option braces are left literal, and a
    balanced ``${...}`` is opaque (masked out before expansion, restored after).

    Expansion is *iterative* (a worklist, not recursion) and bounded by a shared
    ``budget`` — a single-element mutable list holding the number of finished
    patterns still permitted. The caller passes one budget across every glob in a
    membership check, so total expansion is bounded regardless of how a manifest
    splits work across many globs; the transient worklist is bounded too. A
    separate ``work`` budget bounds the *characters scanned* while locating the
    next alternation (see ``_find_expandable_brace``), so a deeply nested singleton
    cannot cost tens of seconds even while producing few finished patterns. Any
    bound exceeded raises ``_BraceBudgetError`` so the caller fails membership
    closed instead of materializing an exponential list — or overflowing the
    recursion stack — from an untrusted manifest (a ``{a,b}`` brace bomb,
    including one with thousands of nested groups or millions of comma options).
    """
    if budget is None:
        budget = [_MAX_BRACE_EXPANSION]
    if work is None:
        work = [_MAX_BRACE_SCAN_WORK]
    if _DOLLAR_MASK in pattern:
        # The mask sentinel cannot appear in a real path/glob; if it does the input
        # cannot be masked safely → fail closed.
        raise _PatternBudgetError
    pattern, literals = _mask_dollar_braces(pattern, work)

    def _emit(value: str) -> None:
        budget[0] -= 1
        if budget[0] < 0:
            raise _BraceBudgetError
        out.append(value)

    out: list = []
    worklist = [pattern]
    while worklist:
        if len(worklist) > budget[0] + 1:
            raise _BraceBudgetError
        pat = worklist.pop()
        span = _find_expandable_brace(pat, budget[0] + 1, work)
        if span is None:
            _emit(pat)  # no real alternation remains → terminal (literal braces)
            continue
        start, end = span
        options = _split_top_level_commas(pat[start + 1:end], budget[0] + 1)
        prefix, suffix = pat[:start], pat[end + 1:]
        for option in options:
            worklist.append(prefix + option + suffix)
    return [_restore_dollar_braces(p, literals) for p in out]


def _package_matches_workspace(rel_parts: Tuple[str, ...], globs: list,
                               cell_budget: Optional[list] = None,
                               work_budget: Optional[list] = None,
                               expand_budget: Optional[list] = None,
                               ordered: bool = True) -> bool:
    """Return True when ``rel_parts`` matches the workspace globs' include/exclude
    semantics. The algorithm depends on the declaring tool (``ordered``):

    * ``ordered=True`` (pnpm's ``@pnpm/matcher``): evaluate in DECLARATION ORDER,
      last matching pattern wins PER PATH — a positive includes, a ``!`` exclusion
      excludes, and a *later* positive RE-INCLUDES only the specific paths it matches
      (``["packages/**", "!packages/legacy/**", "packages/legacy/app"]`` re-includes
      ``packages/legacy/app`` but still excludes its sibling ``packages/legacy/other``).
      This is the default for direct callers.
    * ``ordered=False`` (npm/yarn's ``@npmcli/map-workspaces`` and lerna): npm's
      ``appendNegatedPatterns`` preprocessing — a later POSITIVE pattern whose pattern
      STRING is matched by an earlier ``!`` negation's glob REMOVES that negation
      wholesale, so the same declaration re-includes ``packages/legacy/app`` AND (unlike
      pnpm) its sibling ``packages/legacy/other``, because dropping ``!packages/legacy/**``
      un-excludes the entire subtree. A path is a member iff it matches a surviving
      positive and no surviving negation.

    A path inside any ``node_modules/`` directory is never a member in either mode
    (npm's built-in ``**/node_modules/**`` ignore; pnpm/yarn skip ``node_modules``).

    Brace alternations are expanded before matching (a raw glob matches when any of
    its expansions does). The brace-expansion count (``expand_budget``), the
    brace-scan work (``work_budget``), and the DP-cell count (``cell_budget``) are
    each shared across the whole discovery walk when the caller supplies them, so
    pathological globs at several ancestors cannot each spend a full budget's worth
    of expansion, scanning, or matching.
    """
    if len(globs) > _MAX_RAW_GLOBS:
        return False  # hostile declaration size → membership unproven (fail closed)
    try:
        # Brace-expansion count budget. Shared across the whole walk when supplied
        # (so re-expanding globs at each ancestor cannot sum past the cap);
        # otherwise fresh per call for direct/standalone callers.
        budget = expand_budget if expand_budget is not None else [_MAX_BRACE_EXPANSION]
        # Brace-scan budget (see _expand_braces). Shared across the whole walk when
        # supplied; otherwise fresh per call for direct/standalone callers.
        work = work_budget if work_budget is not None else [_MAX_BRACE_SCAN_WORK]
        # Aggregate DP-cell budget for matching. When the caller supplies one it is
        # shared across the *entire* discovery walk (so re-evaluating the same glob
        # set at each package boundary cannot sum to tens of millions of cells);
        # otherwise a fresh per-call budget is used (direct/standalone callers).
        cells = cell_budget if cell_budget is not None else [_MAX_MATCH_CELLS]
        # Universal built-in exclusion: a path *inside* a ``node_modules/`` directory
        # is never a workspace member in any tool — npm appends ``**/node_modules/**``
        # to its ignore set, and pnpm/yarn ignore ``node_modules`` during package
        # discovery. (Only the *contents* are excluded, matching ``**/node_modules/**``;
        # a leaf directory literally named ``node_modules`` is not itself excluded.)
        if any(part == "node_modules" for part in rel_parts[:-1]):
            return False

        # Parse each declared glob once, IN ORDER, into (negated, concrete-patterns).
        # Brace alternations are expanded here; a positive minimatch comment matches
        # nothing (skipped); an unsupported construct fails membership closed.
        parsed = []  # list[tuple[bool, list[str]]] in declaration order
        for raw in globs:
            # Do NOT strip surrounding whitespace: workspace tools treat it
            # literally, so `" packages/* "` is a package literally named with
            # spaces (a non-match), not a broader `packages/*`. An EMPTY entry is kept
            # (not skipped): under npm's ``appendNegatedPatterns`` an empty positive
            # pattern-string can still match and remove a prior negation
            # (``["packages/**", "!**", ""]`` re-includes ``packages/**``), even though it
            # never matches a non-empty leaf path.
            raw = str(raw)
            # Cheap length guard FIRST — before any O(len) syntax scan — so a hostile
            # megabyte-long glob is rejected without a quadratic pre-scan.
            if len(raw) > _MAX_GLOB_LENGTH:
                raise _PatternBudgetError
            if _raw_glob_unsupported(raw):
                # A construct expansion itself would mishandle (backslash escapes).
                raise _PatternBudgetError
            negated = raw.startswith("!")
            body = raw[1:] if negated else raw
            if body.startswith("!"):
                # Two or more leading ``!`` toggle negation in minimatch (``!!x`` is
                # positive, ``!!!x`` negates again). This matcher does not track that
                # parity, so a multi-bang glob fails membership closed rather than be
                # mis-classified (e.g. treating ``!!!packages/foo`` as a literal and
                # falsely proving membership).
                raise _PatternBudgetError
            # A pattern whose effective form begins with ``#`` is a minimatch comment
            # under DEFAULT minimatch options — which is exactly what npm's
            # ``appendNegatedPatterns`` preprocessing uses (``minimatch(pattern,
            # negatedPattern)``), where the *pattern* arg is comment-parsed. npm's FINAL
            # ``glob`` step, however, matches ``#`` LITERALLY (nocomment). Record the flag
            # (classified after the SAME leading normalization the matcher applies, so
            # ``/#*``/``.//#*`` count) and apply the split semantics per-source below.
            is_comment = _effective_leading(body).startswith("#")
            # npm applies leading normalization (``^\.?/+``) to each RAW pattern EXACTLY
            # ONCE, BEFORE minimatch expands braces — so a slash GENERATED by brace
            # expansion (``{/packages/*,other/*}`` → ``/packages/*``) stays anchored and
            # is NOT re-normalized into ``packages/*``. Strip the body once here, expand
            # the normalized body, and match the expansions as ``pre_normalized``.
            norm_body = _strip_one_leading(body)
            expanded = _expand_braces(norm_body, budget, work)
            # Validate the CONCRETE (expanded) patterns, not the raw glob: brace
            # expansion can create an unsupported construct out of separate
            # alternatives (``{?,x}(foo)`` → ``?(foo)`` extglob) or dissolve an
            # apparent one (``{[,x}]`` → ``[]``, ``x]`` literals). Checking each
            # concrete pattern is faithful to what ``fnmatch`` will actually see.
            for pat in expanded:
                if _concrete_pattern_unsupported(pat):
                    raise _PatternBudgetError
            parsed.append((negated, norm_body, expanded, is_comment))

        def _matches_any(pattern_list, dot: bool = False) -> bool:
            return any(
                _relative_matches_workspace_glob(
                    rel_parts, p, cells, work, pre_normalized=True, dot=dot)
                for p in pattern_list
            )

        if ordered:
            # pnpm (@pnpm/matcher): evaluate in DECLARATION ORDER; the last pattern
            # that matches this path decides — a later positive RE-INCLUDES a path an
            # earlier ``!`` excluded, per-path. pnpm treats ``#`` LITERALLY (only a
            # leading ``!`` is special), so a ``#app`` pattern matches a directory named
            # ``#app`` and re-inclusion works — the npm-preprocessing comment rule does
            # NOT apply here.
            member = False
            for negated, _body, expanded, _is_comment in parsed:
                if _matches_any(expanded):
                    member = not negated
            return member

        # npm/yarn/lerna (@npmcli/map-workspaces): faithful ``appendNegatedPatterns``
        # preprocessing. Walking in order, a later POSITIVE pattern whose pattern STRING
        # is matched by an earlier negation's glob REMOVES that negation, and (a second,
        # symmetric step) each SURVIVING negation prunes any positive PATTERN whose raw
        # string it matches. The removal compares the RAW pattern *string* (braces literal;
        # repeated/trailing ``/`` collapsed as minimatch does) via DEFAULT minimatch, so:
        #   * a ``#``-comment NEGATION matches NOTHING here — it can never be removed by a
        #     positive nor prune one (``["**","!#foo","#foo"]`` keeps ``#foo`` excluded);
        #   * braces expand only for the final concrete-path test
        #     (``["packages/**","!packages/a","packages/{a,b}"]`` excludes ``packages/a``,
        #     includes ``packages/b``);
        #   * a ``*`` in the negation glob matches a literal ``*`` segment of the positive
        #     string (``["packages/**","!packages/*"]`` prunes ``packages/**``).
        # The FINAL ``glob`` step then matches ``#`` LITERALLY (nocomment) and applies the
        # surviving negations as npm's dot:true IGNORE set — so ``packages/*`` excludes a
        # leading-dot ``packages/.shadow`` — while positives use dot:false. A path is a
        # member iff it matches a surviving positive (dot:false) and no surviving negation
        # (dot:true).
        def _raw_parts(norm_body):
            # RAW pattern string as a literal path; drop empty segments so ``//``/trailing
            # ``/`` collapse the way minimatch does for the pattern-vs-pattern comparison.
            return tuple(p for p in norm_body.split("/") if p != "")

        def _string_matched_by(raw_parts, group):
            return any(
                _relative_matches_workspace_glob(
                    raw_parts, np, cells, work, pre_normalized=True)
                for np in group)

        pos_groups = []  # (raw_pos_parts, expansions) for EVERY positive (incl. comments)
        neg_groups = []  # (is_comment, expansions) still in force, declaration order
        for negated, norm_body, expanded, is_comment in parsed:
            raw_parts = _raw_parts(norm_body)
            if negated:
                neg_groups.append((is_comment, expanded))
            else:
                # Reproduce upstream's EXACT mutation order: ``for (i=0; ...; ++i) { if
                # match: splice(i,1) }`` — a ``splice(i)`` then ``++i`` SKIPS the negation
                # shifted into slot ``i``, so an adjacent matching negation survives. A
                # ``#``-comment negation matches nothing and is never removed.
                i = 0
                while i < len(neg_groups):
                    n_comment, grp = neg_groups[i]
                    if (not n_comment) and _string_matched_by(raw_parts, grp):
                        del neg_groups[i]
                    i += 1
                pos_groups.append((raw_parts, expanded))
        # Second step: a surviving NON-comment negation prunes positives it matches.
        positives = []
        for raw_parts, expanded in pos_groups:
            pruned = any(
                (not n_comment) and _string_matched_by(raw_parts, grp)
                for n_comment, grp in neg_groups)
            if not pruned:
                positives.extend(expanded)
        neg_flat = [np for _n_comment, grp in neg_groups for np in grp]
        if not _matches_any(positives):  # positives: dot:false
            return False
        return not _matches_any(neg_flat, dot=True)  # ignores: dot:true
    except (_PatternBudgetError, RecursionError):
        # Pathological pattern from an untrusted manifest (brace bomb, ``**``
        # wall, or deep nesting) → cannot be evaluated safely, so membership is
        # unproven (fail closed).
        return False


def _workspace_root_for(package_dir: Path, cache: Optional[dict] = None,
                        cell_budget: Optional[list] = None,
                        work_budget: Optional[list] = None,
                        expand_budget: Optional[list] = None) -> Optional[Path]:
    """Return the ancestor workspace *root* that ``package_dir`` is a proven member
    of, or ``None`` when it is not a member of any ancestor workspace.

    Membership is proven, not assumed: an ancestor's declared workspace globs
    (npm/yarn ``workspaces``, ``lerna.json`` ``packages``, ``pnpm-workspace.yaml``
    ``packages``) must actually match ``package_dir`` relative to that ancestor,
    honoring ``!`` exclusions and brace expansion. An unrelated package (e.g. a
    vendored ``vendor/tool``) or an explicitly excluded one (e.g. under a pnpm
    ``!**/test/**``) beneath a workspace root is therefore not treated as a
    member. The search never looks above the repository root (``.git``).

    Returning the *declaring root* (not just a boolean) lets the runner walk use
    it as a traversal ceiling, so intermediate independent ``package.json``
    manifests sitting between the leaf and its workspace root do not prematurely
    stop the walk (e.g. a member ``vendor/container/packages/app`` under a root
    glob ``vendor/container/packages/*`` with an unrelated ``vendor/container``
    manifest in between).
    """
    ancestor = package_dir.parent
    for _ in range(80):
        globs = _workspace_globs_for(ancestor, cache)
        if globs:
            # pnpm evaluates include/exclude in order (re-inclusion); npm/yarn/lerna
            # treat an exclusion as terminal. Pick the algorithm by declaring source.
            ordered = _workspace_source_is_pnpm(ancestor)
            try:
                rel_parts = tuple(package_dir.resolve().relative_to(ancestor.resolve()).parts)
            except (ValueError, OSError, RuntimeError):
                rel_parts = ()
            if rel_parts and _package_matches_workspace(
                    rel_parts, globs, cell_budget, work_budget, expand_budget,
                    ordered=ordered):
                return ancestor
        if (ancestor / ".git").exists():
            break
        parent = ancestor.parent
        if parent == ancestor:
            break
        ancestor = parent
    return None


def _belongs_to_ancestor_workspace(package_dir: Path) -> bool:
    """Return True if ``package_dir`` is a proven member of an ancestor JS
    workspace (see :func:`_workspace_root_for`)."""
    return _workspace_root_for(package_dir) is not None


def _is_within(child: Path, parent: Path) -> bool:
    """True if ``child`` is ``parent`` or a descendant of it (after resolving)."""
    try:
        child.resolve().relative_to(parent.resolve())
        return True
    except (ValueError, OSError, RuntimeError):
        return False


def _is_strict_ancestor(ancestor: Path, descendant: Path) -> bool:
    """True if ``ancestor`` is a strict (proper) ancestor of ``descendant``."""
    try:
        rel = descendant.resolve().relative_to(ancestor.resolve())
    except (ValueError, OSError, RuntimeError):
        return False
    return len(rel.parts) > 0


def _lexical_strict_ancestor(ancestor: Path, descendant: Path) -> bool:
    """True if ``ancestor`` is a strict ancestor of ``descendant`` comparing the
    paths *lexically* (no symlink resolution)."""
    try:
        rel = Path(descendant).relative_to(Path(ancestor))
    except ValueError:
        return False
    return len(rel.parts) > 0


def _lexical_repo_root(test_path: Path) -> Optional[Path]:
    """Find the repository root that lexically contains ``test_path``, or ``None``.

    The root is the nearest ``.git`` ancestor that lies at or above the *deepest
    symlinked directory* on the test file's lexical (``abspath``) path. Anchoring
    above the deepest symlink is what makes containment correct in the presence
    of symlinks:

    * A symlinked test directory escaping the repo (``repo/tests -> /outside``,
      only ``repo/.git``) anchors at ``repo``; the resolved path then escapes
      ``repo`` and is refused by :func:`_detect_ts_test_runner`.
    * A symlink whose target is itself a foreign checkout
      (``repo/link -> /outside`` where ``/outside/foreign/.git`` exists, test at
      ``repo/link/foreign/...``) still anchors at ``repo`` — the foreign
      ``.git`` sits *below* the symlink and is ignored — so the foreign config
      is refused.
    * A symlink that stays inside the repository still anchors at ``repo`` and
      the resolved path stays within it, so detection proceeds normally.

    Harmless system symlinks above the repository (e.g. macOS ``/var`` →
    ``/private/var``) are the deepest symlink only when there is no repo-internal
    symlink, in which case no ``.git`` lies above them and this returns ``None``
    (containment simply not required — the ordinary ``.git`` stop in the walk
    governs). The walk runs to the filesystem root (no artificial depth cap), so
    a deeply nested but legitimate repository is still anchored.
    """
    lex = Path(os.path.abspath(str(test_path)))
    # Deepest lexical directory on the path that is a symlink.
    deepest_link: Optional[Path] = None
    parts = lex.parts
    if parts:
        cursor = Path(parts[0])
        for part in parts[1:]:
            cursor = cursor / part
            try:
                if os.path.islink(str(cursor)):
                    deepest_link = cursor
            except OSError:
                pass
    directory = lex.parent
    for _ in range(4096):  # generous bound; real paths hit the fs root far sooner
        above_deepest_link = (
            deepest_link is None or _lexical_strict_ancestor(directory, deepest_link)
        )
        if above_deepest_link and (directory / ".git").exists():
            return directory
        parent = directory.parent
        if parent == directory:
            break
        directory = parent
    return None


_RUNNER_CONFIGS = (
    # (command prefix, (config filenames — in the runner's documented priority
    # order...), spec_only). Each runner supports the full set of JS/TS module
    # extensions (`.js`/`.mjs`/`.cjs`) plus `.json` (Jest) and TS variants
    # (`.ts`/`.mts`/`.cts`); omitting a supported extension causes a real config to
    # be missed and the test to fall back to `npx tsx` or stop at its boundary.
    ("npx playwright test",
     ("playwright.config.ts", "playwright.config.js", "playwright.config.mjs",
      "playwright.config.cjs", "playwright.config.mts", "playwright.config.cts"),
     True),
    ("npx jest --no-coverage --runTestsByPath",
     ("jest.config.js", "jest.config.mjs", "jest.config.cjs", "jest.config.json",
      "jest.config.ts", "jest.config.mts", "jest.config.cts"),
     False),
    ("npx vitest run",
     ("vitest.config.ts", "vitest.config.js", "vitest.config.mjs",
      "vitest.config.cjs", "vitest.config.mts", "vitest.config.cts"),
     False),
)


def _resolved_repo_root(test_path: Path) -> Optional[Path]:
    """Walk the *fully resolved* (canonical) test path up to the nearest ``.git``.

    Unlike the lexical anchor, this is reliable across harmless system symlinks
    (e.g. macOS ``/var`` → ``/private/var``) because every path is canonical, so
    it is the anchor used to bound a runner *config file* that may itself be a
    symlink escaping the repository."""
    try:
        directory = test_path.resolve().parent
    except (OSError, RuntimeError):
        return None
    for _ in range(4096):
        if (directory / ".git").exists():
            return directory
        parent = directory.parent
        if parent == directory:
            break
        directory = parent
    return None


def _config_allowed(config_path: Path, repo_root: Optional[Path]) -> bool:
    """A runner config is adoptable only if its *resolved* path is a regular file
    inside the anchored repository (``repo_root``). This refuses a config file
    that is itself a symlink escaping the repository, and a broken symlink. When
    no repository is anchored (``repo_root is None``) any existing regular file is
    allowed."""
    try:
        real = Path(os.path.realpath(str(config_path)))
        if not real.is_file():
            return False
    except OSError:
        return False
    if repo_root is None:
        return True
    return _is_within(real, repo_root)


_VITE_CONFIG_NAMES = (
    "vite.config.ts", "vite.config.js", "vite.config.mjs",
    "vite.config.cjs", "vite.config.mts", "vite.config.cts",
)


# Runners that execute a PACKAGE BINARY directly (never a package.json script): the
# next non-flag token IS the binary. ``npx vitest`` / ``bunx vitest`` run the vitest
# executable.
_DIRECT_RUNNERS = frozenset({"npx", "bunx", "pnpx"})
# Runners whose bare form (``pnpm vitest``) or ``run <name>`` (``npm run vitest``) invokes
# a package.json SCRIPT — which may be a Vite-only shadow, NOT the vitest binary — so a
# binary is only proven via an explicit exec sub-command (``pnpm exec vitest``,
# ``pnpm dlx vitest``, ``bun x vitest``). A bare command or ``run`` fails CLOSED.
_EXEC_RUNNERS = frozenset({"npm", "pnpm", "yarn", "bun"})
_EXEC_SUBCMDS = frozenset({"exec", "dlx", "x"})
# Boolean runner flags safe to skip. Any OTHER ``-``-prefixed option (an arg-taking flag
# such as ``npx --package`` / ``pnpm --filter``, or an unknown flag) fails closed.
_RUNNER_BOOL_FLAGS = frozenset({"--yes", "-y"})
# Shell control operators that separate command clauses.
_CLAUSE_OPERATORS = frozenset({";", "&", "&&", "|", "||"})
# A package.json script value longer than this is not parsed for vitest — it fails proof
# closed. Real test scripts are short; a ~1 MB no-whitespace value would make the shell
# lexer build one quadratic-cost token. (Bounds the lexing work per script; the ancestor
# walk reads a bounded number of manifests, so the aggregate stays bounded too.)
_MAX_SCRIPT_LEN = 4096


def _binary_after_flags_is_vitest(tokens: list) -> bool:
    """Return True iff the invoked binary (skipping boolean flags) names ``vitest``. An
    arg-taking/unknown flag fails closed, so ``npx --package vitest echo ok`` — where
    ``vitest`` is the option's VALUE, not the binary — is False. A ``--`` options
    terminator is honored: the token right after it is the positional command, so
    ``npm exec -- vitest`` is True."""
    for j, tok in enumerate(tokens):
        if tok == "--":
            nxt = tokens[j + 1] if j + 1 < len(tokens) else ""
            return nxt.split("/")[-1] == "vitest"
        if tok in _RUNNER_BOOL_FLAGS:
            continue
        if tok.startswith("-"):
            return False
        return tok.split("/")[-1] == "vitest"
    return False


def _clause_invokes_vitest(tokens: list) -> bool:
    """True when a single command clause (already tokenized) runs the ``vitest`` binary in
    EXECUTABLE position: as the command itself (basename ``vitest``), via a direct
    package runner (``npx``/``bunx`` + ``vitest``), or via an explicit exec sub-command
    (``pnpm exec vitest``, ``pnpm dlx vitest``, ``bun x vitest``). A bare ``pnpm vitest``
    or a ``run <name>`` form (``npm run vitest``) invokes a package.json SCRIPT — possibly
    a Vite-only shadow — and is NOT proof. Neither is a bare ``vitest`` ARGUMENT
    (``echo vitest``, ``node vitest``, ``command -v vitest``)."""
    idx = 0
    while idx < len(tokens) and re.match(r"^[A-Za-z_][A-Za-z0-9_]*=", tokens[idx]):
        idx += 1  # drop leading VAR=value environment assignments
    if idx >= len(tokens):
        return False
    cmd = tokens[idx].split("/")[-1]
    if cmd == "vitest":
        return True
    if cmd in _DIRECT_RUNNERS:
        return _binary_after_flags_is_vitest(tokens[idx + 1:])
    if cmd in _EXEC_RUNNERS:
        rest = tokens[idx + 1:]
        if rest and rest[0] in _EXEC_SUBCMDS:
            return _binary_after_flags_is_vitest(rest[1:])
        return False  # bare command or `run <name>` → a script, not the binary
    return False


def _strip_shell_comments(script: str) -> str:
    """Remove Bash ``#`` comments from ``script``, preserving quote/escape/newline
    provenance that a token-only view loses. A ``#`` starts a comment ONLY when it is
    unquoted, unescaped, and at a word boundary (start of string, or after unquoted
    whitespace or a control operator); it then runs to the end of THAT line (the
    newline is kept). A quoted (``"# x"``), escaped (``\\#``), or mid-word (``a#b``)
    ``#`` is literal and preserved."""
    out: list = []
    in_single = in_double = False
    at_boundary = True
    i, n = 0, len(script)
    while i < n:
        c = script[i]
        if c == "\\" and not in_single:
            out.append(c)
            if i + 1 < n:
                out.append(script[i + 1])
                i += 2
            else:
                i += 1
            at_boundary = False
            continue
        if c == "'" and not in_double:
            in_single = not in_single
            out.append(c)
            at_boundary = False
            i += 1
            continue
        if c == '"' and not in_single:
            in_double = not in_double
            out.append(c)
            at_boundary = False
            i += 1
            continue
        if c == "#" and not in_single and not in_double and at_boundary:
            while i < n and script[i] != "\n":  # comment to end of THIS line
                i += 1
            continue
        out.append(c)
        at_boundary = c.isspace() or c in ";&|<>()"
        i += 1
    return "".join(out)


def _script_invokes_vitest(script: str) -> bool:
    """True when a package.json script actually INVOKES vitest as a command (in
    executable position, or via a supported ``npx``/``pnpm``/``yarn``/``bun`` runner),
    not merely mentioning the string. Bash ``#`` comments are removed first with full
    quote/escape/newline provenance (see :func:`_strip_shell_comments`) — so a quoted or
    escaped ``#`` is literal, a mid-word ``#`` is literal (``echo a#b && npx vitest``
    proves), and an unquoted comment ends only its own line. Each line is then split into
    command clauses on unquoted control operators (``;`` ``&`` ``&&`` ``|`` ``||``) with a
    QUOTE-/ESCAPE-aware lexer, so ``echo x\\; vitest`` stays one clause. An oversized
    script (a manifest padding attack) and a malformed (unbalanced-quote) script both fail
    closed. A here-document / here-string (``<<``) is refused: its BODY is data, not
    commands, so a ``vitest`` line inside a ``cat <<EOF … EOF`` block must NOT prove
    Vitest, and reliably tracking heredoc body boundaries here is not worth the risk."""
    if len(script) > _MAX_SCRIPT_LEN:
        return False
    if "<<" in script:  # heredoc/here-string body text is not an executed command
        return False
    try:
        for line in _strip_shell_comments(script).split("\n"):
            lex = shlex.shlex(line, posix=True, punctuation_chars=True)
            lex.whitespace_split = True
            lex.commenters = ""  # comments already stripped above
            clause: list = []
            for tok in lex:
                if tok in _CLAUSE_OPERATORS:
                    if _clause_invokes_vitest(clause):
                        return True
                    clause = []
                else:
                    clause.append(tok)
            if _clause_invokes_vitest(clause):
                return True
        return False
    except ValueError:
        return False


def _vitest_proven_by_manifest(manifest: dict) -> bool:
    """True when a ``package.json`` manifest proves Vitest is the test runner — so a
    bare ``vite.config.*`` (which Vitest loads as its config) may be adopted. Proof is
    ``vitest`` declared in any dependency map with a STRING version spec, or a script
    that actually invokes the ``vitest`` command (a token whose basename is ``vitest``).
    Without such proof an ordinary Vite *application* (which also has a ``vite.config.*``
    but no tests, and whose scripts merely mention the string) MUST NOT be treated as a
    test project. A non-string dependency value (``"vitest": false``/``null``/a number) is
    not a valid package spec — npm normalization rejects it — so it does NOT prove Vitest."""
    for key in ("dependencies", "devDependencies",
                "peerDependencies", "optionalDependencies"):
        deps = manifest.get(key)
        if isinstance(deps, dict) and isinstance(deps.get("vitest"), str):
            return True
    scripts = manifest.get("scripts")
    if isinstance(scripts, dict):
        for val in scripts.values():
            if isinstance(val, str) and _script_invokes_vitest(val):
                return True
    return False


def _package_json_runner(search_dir: Path, is_spec: bool,
                         repo_root: Optional[Path]) -> Optional[Tuple[str, Path]]:
    """Fallback runner detection from ``search_dir/package.json`` when no dedicated
    ``jest.config.*``/``vitest.config.*`` file is present:

    * Jest reads its config from a top-level ``"jest"`` object in ``package.json``, so a
      package whose only Jest configuration is that key is still a Jest project.
    * Vitest, only when the manifest *proves* it is in use (see
      :func:`_vitest_proven_by_manifest`), loads ``vite.config.*`` as its config.

    The manifest is read bounded and parsed strictly (npm/Node ``JSON.parse``
    semantics via ``_reject_json_constant``); any malformed/oversized/non-object
    manifest fails closed (``None``). Both the manifest and any adopted
    ``vite.config.*`` are subject to repository containment. (``is_spec`` is
    irrelevant here — Jest/Vitest both run ``.spec`` files; Playwright has no
    ``package.json`` config form.)"""
    manifest_path = search_dir / "package.json"
    if not _config_allowed(manifest_path, repo_root):
        return None
    text = _read_manifest_text(manifest_path)
    if text is None:
        return None
    try:
        manifest = json.loads(text, parse_constant=_reject_json_constant)
    except (ValueError, RecursionError):
        return None
    if not isinstance(manifest, dict):
        return None
    if isinstance(manifest.get("jest"), dict):
        return ("npx jest --no-coverage --runTestsByPath", search_dir)
    if _vitest_proven_by_manifest(manifest):
        for name in _VITE_CONFIG_NAMES:
            cfg = search_dir / name
            if cfg.exists() and _config_allowed(cfg, repo_root):
                return ("npx vitest run", search_dir)
    return None


def _find_runner_here(search_dir: Path, is_spec: bool, repo_root: Optional[Path]) -> Optional[Tuple[str, Path]]:
    """Return the runner ``(command_prefix, search_dir)`` for the highest-priority
    runner config present in ``search_dir`` and allowed by containment, else
    ``None``. Playwright is only considered for ``.spec`` files. A dedicated config
    file wins; otherwise ``package.json`` is consulted for an inline Jest config or a
    proven-Vitest ``vite.config.*``."""
    for command, names, spec_only in _RUNNER_CONFIGS:
        if spec_only and not is_spec:
            continue
        for name in names:
            cfg = search_dir / name
            if cfg.exists() and _config_allowed(cfg, repo_root):
                return (command, search_dir)
    return _package_json_runner(search_dir, is_spec, repo_root)


def _detect_ts_test_runner(test_path: Path) -> Optional[Tuple[str, Path]]:
    """Detect Playwright, Jest, or Vitest config by walking up from the test file.

    For .spec.ts/.spec.tsx files, checks for playwright.config first.
    Returns (command, config_directory) tuple if a config is found, otherwise None.
    The config_directory is where the test runner config lives — callers must use it as cwd.

    The nearest ancestor config wins. The upward walk stops at the JS project
    boundary — the nearest ``package.json`` — rather than after a fixed number of
    parents, so a colocated test many directories below its runner config (e.g. a
    page test under ``frontend/src/app/hackathon/[eventId]/team/__tests__/`` and
    the config at ``frontend/jest.config.js``) still finds it. Two refinements
    keep that boundary correct in monorepos:

    * A *workspace leaf* package has its own ``package.json`` yet inherits its
      runner config from the workspace root, so when the leaf belongs to an
      ancestor workspace (``workspaces`` field / ``pnpm-workspace.yaml`` /
      ``lerna.json``) the walk continues *through* the leaf to the workspace root.
    * An *independent* package must not adopt an unrelated ancestor's config, so
      the walk stops at its ``package.json`` and never crosses the repository root
      (``.git``). A hard iteration cap guards against pathological paths.

    When the leaf is a proven workspace member, the declaring workspace *root*
    becomes a traversal ceiling: intermediate independent ``package.json``
    manifests between the leaf and that root do not stop the walk, so the
    root-level runner config is still reached. A symlinked test directory that
    resolves outside the repository is refused (repository containment) so the
    walk cannot be smuggled into an out-of-repo config.

    Jest is invoked with ``--runTestsByPath`` so the resolved absolute path is
    matched literally (see ``get_test_command_for_file`` for how the path is
    escaped/quoted per runner). Jest otherwise treats the trailing path as a
    regex, and Next.js dynamic-route segments such as ``[eventId]``/``[slug]`` are
    regex character classes that never match the literal bracketed path — leaving
    the generated suite unexecutable.
    """
    # Reject a path where a ``..`` component traverses a symlink: ``os.path.abspath``
    # collapses ``..`` textually, which is unsound across symlinks and would let a
    # crafted path mis-anchor repository containment. When the naive collapse and
    # the true resolution disagree, fail closed.
    try:
        if os.path.realpath(os.path.abspath(str(test_path))) != os.path.realpath(str(test_path)):
            return None
    except OSError:
        return None

    is_spec = test_path.name.endswith(('.spec.ts', '.spec.tsx'))
    try:
        search_dir = test_path.resolve().parent
    except (OSError, RuntimeError):
        # A self-referential (looping) or otherwise unresolvable symlink path →
        # refuse smart-runner discovery rather than crash the caller.
        return None
    # Repository containment: anchor the repo root lexically (before symlinks are
    # resolved). If the resolved test path escapes that root, refuse to adopt any
    # out-of-repo runner config.
    contain = _lexical_repo_root(test_path)
    # Canonical repository of the (real) test file, used to reject a runner config
    # file that is itself a symlink escaping the repository — reliable even where
    # the lexical anchor is unset because of a harmless system symlink above it.
    repo_root = _resolved_repo_root(test_path)
    # Per-discovery cache so each ancestor manifest is parsed at most once even as
    # the walk revisits ancestors through _workspace_root_for (bounds O(n^2) reads).
    ws_cache: dict = {}
    # Per-discovery aggregate DP-cell budget shared across every membership check
    # in this walk, so repeated matching at each package boundary is bounded.
    match_cells: list = [_MAX_MATCH_CELLS]
    # Per-discovery aggregate brace-scan budget, shared the same way, so a repo with
    # a pathological nested-brace glob at several ancestors cannot spend a full
    # scan budget at each level.
    brace_work: list = [_MAX_BRACE_SCAN_WORK]
    # Per-discovery aggregate brace-expansion *count* budget, shared the same way,
    # so a glob that expands to many patterns re-evaluated at every ancestor cannot
    # sum past the cap.
    brace_expand: list = [_MAX_BRACE_EXPANSION]
    # Deepest ancestor-workspace root the original leaf must still reach; walk
    # *through* intermediate independent package.json manifests until then.
    ceiling: Optional[Path] = None
    for _ in range(80):
        # Never step outside the repository (e.g. via a symlink that resolves out).
        if contain is not None and not _is_within(search_dir, contain):
            break
        found = _find_runner_here(search_dir, is_spec, repo_root)
        if found is not None:
            return found
        # Lexical presence: a ``package.json`` that is a *dangling* symlink still
        # marks a JS project boundary. ``Path.exists()`` returns False for it, which
        # would let the walk slip past an independent package and adopt an unrelated
        # ancestor's config — so use ``os.path.lexists`` and fail closed (stop).
        pkg_here = os.path.lexists(str(search_dir / "package.json"))
        # Extend the workspace ceiling from a proven member manifest here — or when
        # we have reached the current ceiling, so a nested workspace root that lacks
        # its own package.json can still chain outward.
        member_root: Optional[Path] = None
        if pkg_here or (ceiling is not None and search_dir == ceiling):
            member_root = _workspace_root_for(
                search_dir, ws_cache, match_cells, brace_work, brace_expand)
            if member_root is not None and (ceiling is None or _is_strict_ancestor(member_root, ceiling)):
                ceiling = member_root
        # Stop at the declaring workspace root, even when it has no package.json of
        # its own (e.g. a pnpm/lerna root). If it was itself proven a member of an
        # outer workspace, ``ceiling`` was extended above and this does not fire.
        if ceiling is not None and search_dir == ceiling:
            break
        # Independent JS project boundary that is not a workspace member and not
        # below the ceiling → stop.
        if pkg_here:
            below_ceiling = ceiling is not None and _is_strict_ancestor(ceiling, search_dir)
            if member_root is None and not below_ceiling:
                break
        # Never escape the repository, even absent an in-project config.
        if (search_dir / ".git").exists():
            break
        parent = search_dir.parent
        if parent == search_dir:
            break
        search_dir = parent
    return None


def _load_language_format() -> dict:
    """Load language_format.csv into a dict keyed by extension."""
    # Try multiple paths: package-relative first, then project-root-relative
    candidates = [
        Path(__file__).parent / "data" / "language_format.csv",
        Path(__file__).parent.parent / "data" / "language_format.csv",
    ]
    for csv_path in candidates:
        if csv_path.exists():
            result = {}
            with open(csv_path, 'r') as f:
                reader = csv.DictReader(f)
                for row in reader:
                    ext = row.get('extension', '')
                    if ext:
                        result[ext] = row
            return result
    # CSV not found - return empty dict so smart detection (step 2) can handle it
    return {}


def get_test_command_for_file(test_file: str, language: Optional[str] = None) -> Optional[TestCommand]:
    """
    Get the appropriate test command for a test file.

    Resolution order:
    1. For TS/TSX: smart runner detection via _detect_ts_test_runner() which returns
       both the command and the config directory (cwd). Critical for monorepos where
       test runner configs live in subdirectories (e.g., frontend/jest.config.js).
    2. CSV run_test_command (if non-empty).
    3. Smart detection via default_verify_cmd_for().
    4. None (triggers agentic fallback)

    Args:
        test_file: Path to the test file
        language: Optional language override

    Returns:
        TestCommand with command string and optional cwd, or None
    """
    test_path = Path(test_file)
    ext = test_path.suffix

    resolved_language = language
    if resolved_language is None:
        resolved_language = get_language(ext)

    # 1. For TypeScript/TSX: detect Jest or Vitest config and use appropriate runner
    if ext in ('.ts', '.tsx') and resolved_language and resolved_language.lower() in ('typescript', 'typescriptreact'):
        runner_result = _detect_ts_test_runner(test_path)
        if runner_result:
            runner_cmd, config_dir = runner_result
            resolved = str(test_path.resolve())
            # Playwright treats its positional argument as a regular expression, so
            # a literal path (e.g. a Next.js dynamic route like ``[slug]``) must be
            # regex-escaped to match. Jest ``--runTestsByPath`` and Vitest take the
            # path literally. In every case the argument is shell-quoted because
            # callers run the command string with ``shell=True`` — an unquoted path
            # with spaces or shell metacharacters would otherwise be re-split or
            # (for bracket globs / ``$()``) reinterpreted by the shell.
            #
            # ``command`` is a POSIX-shell command string, matching how every pdd
            # caller executes verify commands (``subprocess.run(..., shell=True)``
            # or ``shlex.split``). ``shlex.quote`` is therefore the correct quoting
            # here. Making runner execution safe under Windows ``cmd.exe`` would
            # require moving all callers to an argv list + ``shell=False`` — a
            # pre-existing, cross-cutting change to pdd's command-as-string
            # convention that is out of scope for runner detection.
            if runner_cmd.startswith("npx playwright"):
                target = shlex.quote(re.escape(resolved))
            else:
                target = shlex.quote(resolved)
            return TestCommand(command=f"{runner_cmd} {target}", cwd=config_dir)

    # 2. Check CSV for run_test_command
    lang_formats = _load_language_format()
    if ext in lang_formats:
        csv_cmd = lang_formats[ext].get('run_test_command', '').strip()
        if csv_cmd:
            # Shell-quote the substituted path via a shell-lexical-aware single pass:
            # callers run this string with ``shell=True``, so an unquoted path with
            # metacharacters (``/repo/$(touch PWN)/a.test.ts``) would be re-split or
            # command-substituted. ``shlex.quote`` is only safe at a bare word, so a
            # CSV template that quotes ``{file}`` (``mocha "{file}"``) is refused
            # (fall through to smart detection) rather than made injectable.
            substituted = shell_safe_substitute(csv_cmd, {'{file}': str(test_file)})
            if substituted is not None:
                return TestCommand(command=substituted)

    # 3. Smart detection
    if resolved_language:
        smart_cmd = default_verify_cmd_for(resolved_language.lower(), str(test_file))
        if smart_cmd:
            return TestCommand(command=smart_cmd)

    # 4. No command available
    return None
