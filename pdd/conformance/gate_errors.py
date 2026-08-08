"""Typed exceptions raised by the PDD conformance gates.

Extracted from ``code_generator_main`` so ``sync_main``, ``sync_orchestration``,
``one_session_sync``, ``cmd_test_main`` and ``agentic_test_generate`` can catch
these types without importing the generation pipeline. The four message prefixes
are a cross-process contract string-matched by ``agentic_sync_runner`` on child
stdout and must stay byte-identical.
"""

import json
import os
import re
from typing import Any, Dict, List, Optional, Tuple

import click


# Extensions for languages that follow the `<name>_test.<ext>` /
# `<name>_spec.<ext>` sibling-file convention (file lives next to
# production code, not under `tests/`). Used by
# `_is_test_output_path` so the test-churn gate auto-covers any
# supported language whose test runner picks up that pattern. Adding
# a new language with this naming convention to `language_format.csv`
# should also be appended here; doing so eliminates the
# `_is_test_output_path` extension-by-extension fix cycle (see PR
# #1015 external review iter-12 follow-ups). PascalCase JVM/.NET/
# Swift conventions (`FooTest.java`, `WidgetSpec.kt`) are matched
# separately to keep the check case-sensitive and dodge
# `latest.kt`-style false positives.
_LANGUAGE_TEST_FILE_EXTS: Tuple[str, ...] = (
    ".py",
    ".go",
    ".rb",
    ".rs",
    ".exs",
    ".ex",
    ".dart",
    ".clj",
    ".cljc",
    ".lua",
    ".php",
)

PROSE_OUTPUT_REPAIR_DIRECTIVE = (
    "The previous response contained no extractable code. Return the complete "
    "source file only, inside a single code block. Do not include any planning "
    "text, prose explanation, or partial snippets outside the code block."
)

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
        signature_details: Optional[List[Tuple[str, str, str, str]]] = None,
    ) -> None:
        self.prompt_name = prompt_name
        self.output_path = output_path or ""
        self.removed_symbols = list(removed_symbols)
        self.changed_signatures = list(changed_signatures or [])
        self.pre_surface_size = int(pre_surface_size)
        self.post_surface_size = int(post_surface_size)
        self.total_cost = float(total_cost or 0.0)
        self.model_name = model_name or "unknown"
        # Structured per-symbol detail for signature mismatches (issue #1900):
        # ``(symbol, expected_entry, actual_entry, source)`` where ``source`` is
        # ``"pdd-interface"`` when the expected signature came from the prompt's
        # declaration. Purely additive — the ``removed:`` / ``signature_changed:``
        # message lines below stay byte-for-byte identical (the cloud parser and
        # ~50 tests key on them).
        self.signature_details = list(signature_details or [])
        self._repair_directive_override = repair_directive
        output_display = self.output_path or "<unknown>"
        message_lines = [
            f"Public surface regression for {prompt_name}:",
            f"removed: {', '.join(self.removed_symbols) if self.removed_symbols else '<none>'}",
            f"signature_changed: {', '.join(self.changed_signatures) if self.changed_signatures else '<none>'}",
            f"output: {output_display}",
            f"pre_surface_size: {self.pre_surface_size}",
            f"post_surface_size: {self.post_surface_size}",
        ]
        # Append (never alter the lines above) one structured detail line per
        # signature mismatch so the full expected-vs-actual contract is carried
        # in the message the local + cloud repair loops read. JSON-encoded so a
        # signature/default containing the old ` | ` field delimiters can't corrupt
        # parsing (codex round-8 finding 2); parsed by
        # ``agentic_sync_runner._parse_signature_detail_lines``.
        for symbol, expected_entry, actual_entry, source in self.signature_details:
            message_lines.append(
                "signature_detail: "
                + json.dumps(
                    {
                        "symbol": symbol,
                        "expected": expected_entry,
                        "actual": actual_entry,
                        "source": source,
                    }
                )
            )
        super().__init__("\n".join(message_lines))

    @property
    def repair_directive(self) -> str:
        if self._repair_directive_override:
            return self._repair_directive_override
        lines = ["Public surface regression repair required."]
        if self.removed_symbols:
            lines.append("Restore these public symbols from the existing module:")
            for sym in self.removed_symbols:
                lines.append(f"- {sym}")
        # Prefer the DECLARED signature as the repair target when the prompt's
        # <pdd-interface> is the source of truth: it is a stable target, unlike
        # "restore compatible signatures" (compatible with the very code being
        # regenerated) which dead-ended the change->sync loop (issue #1900).
        declared_details = [
            detail for detail in self.signature_details if detail[3] == "pdd-interface"
        ]
        if declared_details:
            # Inject the DECLARED signature as a VERBATIM hard constraint, not
            # just a description of the violation (issue #1968): an annotation-
            # level drift (declared `object`, regenerated `Any`; or a broadened
            # param union) converges only when the retry is told to reproduce the
            # declared annotation text token-for-token instead of a semantically
            # "equivalent" spelling it keeps re-emitting.
            lines.append(
                "Restore these public symbols to their declared "
                "<pdd-interface> signatures — emit each declared signature "
                "VERBATIM. Reproduce the declared annotation text token-for-"
                "token; do not substitute an equivalent-but-differently-spelled "
                "type (keep `object` as `object`; never emit `Any` where the "
                "declaration says `object`) and do not broaden a declared "
                "parameter's type with `|` union members the declaration omits:"
            )
            for symbol, expected_entry, actual_entry, _ in declared_details:
                lines.append(
                    f"- Restore `{symbol}` to its declared signature "
                    f"`{expected_entry}` (found `{actual_entry}`). Emit exactly "
                    f"`{expected_entry}` — the prior attempt emitted "
                    f"`{actual_entry}`, which differs only in annotation "
                    f"spelling and was rejected."
                )
            # Declaration-aware guidance (codex round-7 finding 3): a declared
            # PARAM change is authorized by EDITING the declaration, not by a
            # BREAKING-CHANGE marker (which only relaxes the un-declarable
            # binding-kind/async for declared symbols) — advising the marker here
            # would loop the user back into the dead-end #1900 removes.
            lines.append(
                "If a declared parameter change is intended, edit the prompt's "
                "<pdd-interface> declaration to the intended signature (the "
                "declaration is the contract for declared symbols)."
            )
        declared_changed = {detail[0] for detail in declared_details}
        remaining_changed = [
            sym for sym in self.changed_signatures if sym not in declared_changed
        ]
        if remaining_changed:
            lines.append("Restore compatible signatures for these public symbols:")
            for sym in remaining_changed:
                lines.append(f"- {sym}")
        lines.append(
            "Preserve backward-compatible public helpers unless the prompt lists "
            "the intended removals with BREAKING-CHANGE: remove <symbol>."
        )
        return "\n".join(lines)

_CHURN_NONCE_ENV = "PDD_CHURN_NONCE_FD"

_CHURN_NONCE_CACHE: Optional[str] = None

_CHURN_NONCE_READ = False

def _read_churn_nonce() -> str:
    """Read the one-time provenance nonce the PARENT sync runner handed this child
    over a NON-inherited pipe FD (issue #1903 §B.4 review round 8).

    The parent passes the read-end FD number via ``PDD_CHURN_NONCE_FD`` and keeps
    the FD out of any grandchild test subprocess (``close_fds`` default), so only
    THIS trusted child process can read the nonce. Stamping it into the churn
    block lets the parent distinguish a genuine PDD-emitted block from one a
    hostile project test merely printed to stdout (which cannot know the nonce).
    Read once (the pipe yields EOF afterwards) and cached. Returns ``""`` when no
    channel is present (standalone ``pdd test``/``sync`` — which never
    never-blocks — or an older parent). Total: any error yields ``""``.
    """
    global _CHURN_NONCE_CACHE, _CHURN_NONCE_READ  # pylint: disable=global-statement
    if _CHURN_NONCE_READ:
        return _CHURN_NONCE_CACHE or ""
    _CHURN_NONCE_READ = True
    fd_s = os.environ.get(_CHURN_NONCE_ENV)
    if not fd_s:
        _CHURN_NONCE_CACHE = ""
        return ""
    try:
        fd = int(fd_s)
        chunks = []
        while len(b"".join(chunks)) < 256:
            data = os.read(fd, 256)
            if not data:
                break
            chunks.append(data)
        token = b"".join(chunks).decode("ascii", "ignore").strip()
        # Accept only a plausible hex nonce so a coincidental FD-number collision
        # in some process cannot inject arbitrary bytes as a "valid" nonce.
        _CHURN_NONCE_CACHE = token if re.fullmatch(r"[0-9a-f]{8,128}", token) else ""
    except (OSError, ValueError):
        _CHURN_NONCE_CACHE = ""
    return _CHURN_NONCE_CACHE or ""

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
        adopted_human: bool = False,
    ) -> None:
        self.prompt_name = prompt_name
        self.output_path = output_path or ""
        self.churn_ratio = float(churn_ratio)
        self.threshold = float(threshold)
        self.pre_line_count = int(pre_line_count)
        self.post_line_count = int(post_line_count)
        self.total_cost = float(total_cost or 0.0)
        self.model_name = model_name or "unknown"
        # Issue #1903 §B.4 provenance: True only when this test was ADOPTED from
        # an existing HUMAN co-located test (unpinned), determined at path
        # resolution BEFORE generation. The issue-driven never-block requires it;
        # a False value keeps the strict hard-fail. Serialized into the block so
        # the (subprocess-boundary) parent runner can read it.
        self.adopted_human = bool(adopted_human)
        self._repair_directive_override = repair_directive
        output_display = self.output_path or "<unknown>"
        # Stamp the parent-issued nonce (round 8) so the parent can authenticate
        # THIS block as genuinely PDD-emitted; a forged block printed by a hostile
        # project test cannot carry the correct (secret) nonce and is refused.
        nonce = _read_churn_nonce()
        nonce_line = f"\nnonce: {nonce}" if nonce else ""
        super().__init__(
            f"Test churn threshold exceeded for {prompt_name}:\n"
            f"ratio: {self.churn_ratio:.2f}\n"
            f"threshold: {self.threshold:.2f}\n"
            f"output: {output_display}\n"
            f"pre_line_count: {self.pre_line_count}\n"
            f"post_line_count: {self.post_line_count}\n"
            f"adopted: {str(self.adopted_human).lower()}"
            f"{nonce_line}"
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

class ProseOutputError(click.UsageError):
    """Raised when generation produced no extractable source code."""

    def __init__(
        self,
        prompt_name: str,
        output_path: str,
        language: str,
        model_name: str = "unknown",
        total_cost: float = 0.0,
        raw_output: Optional[str] = None,
        extractor_result: str = "empty",
    ) -> None:
        self.prompt_name = prompt_name
        self.output_path = output_path or ""
        self.language = language or "unknown"
        self.model_name = model_name or "unknown"
        self.total_cost = float(total_cost or 0.0)
        self.extractor_result = extractor_result or "empty"
        raw = "" if raw_output is None else str(raw_output)
        excerpt = raw.strip()
        if not excerpt:
            excerpt = "<empty>"
        elif len(excerpt) > 240:
            excerpt = excerpt[:237] + "..."
        self.raw_output_excerpt = excerpt
        output_display = self.output_path or "<unknown>"
        super().__init__(
            f"Generation output extraction failure for {prompt_name}:\n"
            f"model_name: {self.model_name}\n"
            f"language: {self.language}\n"
            f"output: {output_display}\n"
            f"Extractor result: {self.extractor_result}\n"
            f"Raw output excerpt: {self.raw_output_excerpt}"
        )

    @property
    def repair_directive(self) -> str:
        return PROSE_OUTPUT_REPAIR_DIRECTIVE
