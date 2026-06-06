"""Phase-aware compressed context packages for sync workflows."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Mapping, Sequence
from xml.sax.saxutils import escape


DEFAULT_BUDGET = 12000
# Reserve space for XML wrapper + compact metadata in render_for_prompt().
_RENDER_WRAPPER_RESERVE = 320
_SECRET_PATTERNS = [
    re.compile(r"(?i)(bearer\s+)[A-Za-z0-9._~+/=-]+"),
    re.compile(r"(?i)(api[_-]?key\s*[=:]\s*)[^\s,;]+"),
    re.compile(r"(?i)(token\s*[=:]\s*)[^\s,;]+"),
    re.compile(r"(?i)(secret\s*[=:]\s*)[^\s,;]+"),
    re.compile(r"(?i)(authorization\s*:\s*)[^\n]+"),
    re.compile(r"(?i)(https?://[^:\s/]+:)[^@\s/]+(@)"),
]


@dataclass(frozen=True)
class CompressedSyncContext:
    """Bounded supplemental context for one sync phase."""

    enabled: bool
    used: bool
    phase: str
    content: str = ""
    source_paths: list[str] = field(default_factory=list)
    source_hashes: dict[str, str] = field(default_factory=dict)
    compressed_sha256: str = ""
    source_count: int = 0
    char_count: int = 0
    token_estimate: int = 0
    budget: int = DEFAULT_BUDGET
    unavailable_reason: str | None = None
    missing_sources: list[str] = field(default_factory=list)
    mode: str = "compressed-sync-context"


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _redact(value: str) -> str:
    text = value
    for pattern in _SECRET_PATTERNS:
        text = pattern.sub(lambda match: f"{match.group(1)}[REDACTED]{match.group(2) if match.lastindex and match.lastindex >= 2 else ''}", text)
    return text


def _read_source(path: str | Path | None, label: str, missing: list[str]) -> tuple[str, str] | None:
    if not path:
        return None
    source_path = Path(path)
    if not source_path.exists() or not source_path.is_file():
        missing.append(f"{label}:{source_path}")
        return None
    content = _redact(source_path.read_text(encoding="utf-8", errors="replace"))
    return str(source_path), content


def _prompt_contract_excerpt(content: str) -> str:
    sections: list[str] = []
    for tag in (
        "pdd-interface",
        "responsibility",
        "non_responsibilities",
        "vocabulary",
        "contract_rules",
        "capabilities",
        "coverage",
    ):
        for match in re.finditer(rf"<{tag}\b[^>]*>.*?</{tag}>", content, re.DOTALL | re.IGNORECASE):
            sections.append(match.group(0).strip())
    if sections:
        return "\n\n".join(sections)
    return content[:4000]


def _clip(label: str, content: str, budget: int) -> str:
    if budget <= 0:
        return ""
    if len(content) <= budget:
        return f"<{label}>\n{content}\n</{label}>"
    head = max(budget // 2, 1)
    tail = max(budget - head, 1)
    clipped = f"{content[:head]}\n...[compressed {len(content) - budget} chars omitted]...\n{content[-tail:]}"
    return f"<{label}>\n{clipped}\n</{label}>"


def _render_sources_within_budget(
    sources: list[tuple[str, str, str]],
    budget: int,
) -> str:
    """Clip and join sources so the combined payload stays within ``budget`` chars."""
    active = [(path, label, content.strip()) for path, label, content in sources if content.strip()]
    if not active or budget <= 0:
        return ""
    count = len(active)
    separator = "\n\n"
    separator_overhead = len(separator) * max(count - 1, 0)

    def _build(per_source: int) -> str:
        parts = [
            _clip(label.replace("-", "_"), content, max(per_source, 1))
            for _, label, content in active
            if max(per_source, 1) > 0
        ]
        return separator.join(part for part in parts if part)

    per_source = max((budget - separator_overhead) // count, 1)
    rendered = _build(per_source)
    while len(rendered) > budget and per_source > 1:
        per_source = max(per_source // 2, 1)
        rendered = _build(per_source)
    if len(rendered) > budget:
        rendered = rendered[:budget]
    return rendered


def compressed_context_is_active(context: CompressedSyncContext | Mapping[str, Any] | None) -> bool:
    """Return True when a sync compressed-context package should replace full expansions."""
    if context is None:
        return False
    data = asdict(context) if isinstance(context, CompressedSyncContext) else dict(context)
    return bool(data.get("used"))


def build_compressed_sync_context(
    phase: str,
    prompt_path: str | Path,
    code_path: str | Path | None = None,
    example_path: str | Path | None = None,
    test_paths: Sequence[str | Path] | None = None,
    run_report_path: str | Path | None = None,
    contract_summary: Mapping[str, Any] | None = None,
    repair_directive: str | None = None,
    budget: int | None = None,
) -> CompressedSyncContext:
    """Build a deterministic, bounded context package for a sync phase."""
    effective_budget = int(budget or DEFAULT_BUDGET)
    missing: list[str] = []
    sources: list[tuple[str, str, str]] = []

    prompt_source = _read_source(prompt_path, "prompt", missing)
    if prompt_source is None:
        return CompressedSyncContext(
            enabled=True,
            used=False,
            phase=phase,
            budget=effective_budget,
            unavailable_reason="prompt source missing",
            missing_sources=missing,
        )
    prompt_label, prompt_content = prompt_source
    sources.append((prompt_label, "prompt_contract", _prompt_contract_excerpt(prompt_content)))

    for label, path in (("code", code_path), ("example", example_path), ("run_report", run_report_path)):
        source = _read_source(path, label, missing)
        if source is not None:
            source_path, content = source
            sources.append((source_path, label, content))

    for idx, test_path in enumerate(test_paths or []):
        source = _read_source(test_path, f"test{idx}", missing)
        if source is not None:
            source_path, content = source
            sources.append((source_path, "test", content))

    if contract_summary:
        sources.append((
            "contract_summary",
            "contract_summary",
            _redact(json.dumps(contract_summary, sort_keys=True, default=str)),
        ))
    if repair_directive and repair_directive.strip():
        sources.append(("repair_directive", "repair_directive", _redact(repair_directive.strip())))

    content_budget = max(effective_budget - _RENDER_WRAPPER_RESERVE, 1)
    content = _render_sources_within_budget(sources, content_budget)
    return CompressedSyncContext(
        enabled=True,
        used=bool(content),
        phase=phase,
        content=content,
        source_paths=[path for path, _, _ in sources if path not in {"contract_summary", "repair_directive"}],
        source_hashes={path: _sha256_text(content) for path, _, content in sources},
        compressed_sha256=_sha256_text(content) if content else "",
        source_count=len(sources),
        char_count=len(content),
        token_estimate=max(1, len(content) // 4) if content else 0,
        budget=effective_budget,
        unavailable_reason=None if content else "no usable context",
        missing_sources=missing,
    )


def metadata(context: CompressedSyncContext | Mapping[str, Any]) -> dict[str, Any]:
    """Return manifest-safe metadata with raw content omitted."""
    data = asdict(context) if isinstance(context, CompressedSyncContext) else dict(context)
    data.pop("content", None)
    return data


def _compact_render_metadata(data: Mapping[str, Any]) -> str:
    """Manifest-safe metadata for the rendered XML block (no raw content)."""
    return escape(
        json.dumps(
            {
                "phase": data.get("phase"),
                "compressed_sha256": data.get("compressed_sha256"),
                "source_count": data.get("source_count"),
                "char_count": data.get("char_count"),
                "budget": data.get("budget"),
            },
            sort_keys=True,
            default=str,
        )
    )


def _render_prompt_block(phase: str, meta_text: str, body: str) -> str:
    return (
        f'<compressed_sync_context phase="{phase}">\n'
        f"<metadata>{meta_text}</metadata>\n"
        f"<content>\n{body}\n</content>\n"
        "</compressed_sync_context>\n"
    )


def render_for_prompt(context: CompressedSyncContext | Mapping[str, Any] | None) -> str:
    """Render a compressed context package as a safe XML prompt supplement."""
    if context is None:
        return ""
    data = asdict(context) if isinstance(context, CompressedSyncContext) else dict(context)
    if not data.get("used") or not data.get("content"):
        return ""
    effective_budget = int(data.get("budget") or DEFAULT_BUDGET)
    phase = escape(str(data.get("phase", "")))
    meta_text = _compact_render_metadata(data)
    raw_content = str(data.get("content", ""))

    low, high = 0, len(raw_content)
    best = ""
    while low <= high:
        mid = (low + high) // 2
        rendered = _render_prompt_block(phase, meta_text, escape(raw_content[:mid]))
        if len(rendered) <= effective_budget:
            best = rendered
            low = mid + 1
        else:
            high = mid - 1
    return best
