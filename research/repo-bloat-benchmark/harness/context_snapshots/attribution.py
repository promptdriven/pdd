"""Content attribution: which parts of a context snapshot are distractor bulk?

Implements the analysis half of design.md §6.2 tap 1: match the content that
was surfaced into model requests against the materialized tree + manifest, and
attribute spans to ``core`` / ``distractor`` / ``unknown``.

Method: a normalized-line index. Every sufficiently long line of every
materialized file is normalized (whitespace-collapsed) and indexed with its
origin class. Request text is then scanned line-by-line against the index.

Honesty notes (mirrored in the design):

- Attribution is a **lower bound**: paraphrased or heavily truncated content
  does not match. The provider ``usage`` numbers remain the authoritative
  token totals; attribution only splits them.
- Token counts here are **estimates** under a pluggable tokenizer (default:
  chars/4). The reconciliation step caps attributed tokens at the provider
  count so attribution can never exceed measurement.
- Lines shorter than ``min_line_len`` (import boilerplate, ``return None``)
  are ignored to avoid false-positive matches; a line appearing in both a
  core and a distractor file counts as ``ambiguous`` and is excluded from the
  distractor total (conservative direction).
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Iterable

_WHITESPACE = re.compile(r"\s+")


def default_token_estimator(text: str) -> float:
    """Crude but deterministic token estimate (~4 chars/token)."""
    return len(text) / 4.0


def normalize_line(line: str) -> str:
    return _WHITESPACE.sub(" ", line.strip())


@dataclass
class Attribution:
    """Per-text attribution result (token estimates, not provider counts)."""

    core_tokens: float = 0.0
    distractor_tokens: float = 0.0
    ambiguous_tokens: float = 0.0
    unknown_tokens: float = 0.0
    core_lines: int = 0
    distractor_lines: int = 0
    ambiguous_lines: int = 0
    unknown_lines: int = 0
    distractor_files: set[str] = field(default_factory=set)
    core_files: set[str] = field(default_factory=set)

    @property
    def total_tokens(self) -> float:
        return (
            self.core_tokens
            + self.distractor_tokens
            + self.ambiguous_tokens
            + self.unknown_tokens
        )

    @property
    def distractor_share(self) -> float:
        total = self.total_tokens
        return self.distractor_tokens / total if total > 0 else 0.0


class TreeIndex:
    """Normalized-line index over a materialized variant tree.

    ``distractor_paths`` is the manifest's secret label key (paths relative to
    the tree root); every other indexed file is core. The index is built once
    per (scenario, size) and reused across trials.
    """

    def __init__(
        self,
        root: str | Path,
        distractor_paths: Iterable[str],
        min_line_len: int = 24,
        token_estimator: Callable[[str], float] = default_token_estimator,
        extensions: tuple[str, ...] = (".py", ".md", ".txt", ".toml", ".cfg", ".json"),
    ) -> None:
        self.root = Path(root)
        self.min_line_len = min_line_len
        self.token_estimator = token_estimator
        self._distractors = {p.replace("\\", "/") for p in distractor_paths}
        # normalized line -> (has_core, has_distractor, first core path, first distractor path)
        self._index: dict[str, list] = {}
        for file_path in sorted(self.root.rglob("*")):
            if not file_path.is_file() or file_path.suffix not in extensions:
                continue
            rel = file_path.relative_to(self.root).as_posix()
            is_distractor = rel in self._distractors
            try:
                text = file_path.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            for line in text.splitlines():
                norm = normalize_line(line)
                if len(norm) < self.min_line_len:
                    continue
                entry = self._index.setdefault(norm, [False, False, None, None])
                if is_distractor:
                    entry[1] = True
                    if entry[3] is None:
                        entry[3] = rel
                else:
                    entry[0] = True
                    if entry[2] is None:
                        entry[2] = rel

    @property
    def distractor_paths(self) -> set[str]:
        return set(self._distractors)

    def classify_text(self, text: str) -> Attribution:
        """Attribute one blob of surfaced text (e.g. one request body)."""
        result = Attribution()
        for line in text.splitlines():
            norm = normalize_line(line)
            if len(norm) < self.min_line_len:
                continue
            tokens = self.token_estimator(norm)
            entry = self._index.get(norm)
            if entry is None:
                result.unknown_tokens += tokens
                result.unknown_lines += 1
            elif entry[0] and entry[1]:
                result.ambiguous_tokens += tokens
                result.ambiguous_lines += 1
            elif entry[1]:
                result.distractor_tokens += tokens
                result.distractor_lines += 1
                result.distractor_files.add(entry[3])
            else:
                result.core_tokens += tokens
                result.core_lines += 1
                result.core_files.add(entry[2])
        return result

    def classify_request_payload(self, payload_bytes: bytes) -> Attribution:
        """Attribute a raw archived request body (JSON or free text)."""
        text = payload_bytes.decode("utf-8", errors="replace")
        return self.classify_text(text)


def reconcile_with_usage(
    attribution: Attribution, provider_input_tokens: int | None
) -> dict[str, float]:
    """Scale attribution so it can never exceed the provider-reported input.

    Returns a dict with ``distractor_context_tokens`` (reconciled),
    ``distractor_context_share``, and the raw estimate for transparency.
    If provider usage is unavailable, the raw estimates are used and flagged.
    """
    raw = attribution.distractor_tokens
    total_est = attribution.total_tokens
    if provider_input_tokens is None or total_est <= 0:
        return {
            "distractor_context_tokens": raw,
            "distractor_context_share": attribution.distractor_share,
            "raw_estimate_tokens": raw,
            "reconciled_against_usage": False,
        }
    scale = min(1.0, provider_input_tokens / total_est)
    reconciled = raw * scale
    return {
        "distractor_context_tokens": min(reconciled, float(provider_input_tokens)),
        "distractor_context_share": min(1.0, reconciled / provider_input_tokens)
        if provider_input_tokens
        else 0.0,
        "raw_estimate_tokens": raw,
        "reconciled_against_usage": True,
    }
