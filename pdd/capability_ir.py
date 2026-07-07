from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Literal


@dataclass(frozen=True)
class EffectItem:
    modal: Literal['MAY', 'MUST_NOT']
    action: str
    resource: str


@dataclass
class ContractEffectIR:
    capabilities_present: bool
    effect_count: int
    effects: list[EffectItem]


_BULLET_RE = re.compile(r'^\s*[-*]\s+(MAY|MUST NOT)\s+(\S+)\s+(.*)$', re.IGNORECASE)
_SPLIT_RE = re.compile(r'(?:,\s+|\s+or\s+|\s+and\s+)')
_LEADING_ARTICLE_RE = re.compile(r'^(?:the|a|an)\s+', re.IGNORECASE)


def _is_comment_line(line: str) -> bool:
    return bool(re.match(r'^#(?!#)(?:\s|$)', line))


def _looks_like_inner_capabilities_text(text: str) -> bool:
    """Return True when tagless input is only capability bullets/comments."""
    saw_content = False
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or _is_comment_line(line):
            continue
        saw_content = True
        if not re.match(r'^[-*]\s+', line):
            return False
    return saw_content


def _normalize_resource(resource_raw: str) -> str:
    resource_raw = resource_raw.lower().strip()
    if resource_raw.endswith('.'):
        resource_raw = resource_raw[:-1]
    resource_raw = _LEADING_ARTICLE_RE.sub('', resource_raw).strip()

    parts = _SPLIT_RE.split(resource_raw, maxsplit=1)
    resource_primary = parts[0].strip()

    words = resource_primary.split()
    if any(word.rstrip('s') == 'secret' for word in words):
        return 'secrets'
    if any(word.rstrip('s') == 'email' for word in words):
        return 'email'

    return re.sub(r'\s+', '_', resource_primary)


def parse_capabilities_ir(text: str) -> ContractEffectIR:
    """
    Parses capabilities tag text into a target-neutral effect IR.
    """
    if not text:
        return ContractEffectIR(capabilities_present=False, effect_count=0, effects=[])

    # Strip the outer XML tag if present
    tag_match = re.search(r'<capabilities>(.*?)</capabilities>', text, flags=re.DOTALL | re.IGNORECASE)
    if tag_match:
        inner_text = tag_match.group(1)
    else:
        if not _looks_like_inner_capabilities_text(text):
            return ContractEffectIR(capabilities_present=False, effect_count=0, effects=[])
        inner_text = text

    effects: list[EffectItem] = []

    for line in inner_text.splitlines():
        line = line.strip()
        if not line or _is_comment_line(line):
            continue

        match = _BULLET_RE.match(line)
        if not match:
            continue

        modal_raw = match.group(1).upper()
        if modal_raw == 'MAY':
            modal: Literal['MAY', 'MUST_NOT'] = 'MAY'
        elif modal_raw == 'MUST NOT':
            modal = 'MUST_NOT'
        else:
            continue  # Unrecognized modal, skip

        action = match.group(2).lower()
        resource = _normalize_resource(match.group(3))

        effects.append(EffectItem(
            modal=modal,
            action=action,
            resource=resource
        ))

    return ContractEffectIR(
        capabilities_present=len(effects) > 0,
        effect_count=len(effects),
        effects=effects
    )
