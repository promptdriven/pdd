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


def parse_capabilities_ir(text: str) -> ContractEffectIR:
    """
    Parses capabilities tag text into a target-neutral effect IR.
    
    Extracts the modal, action, and normalized resource from bulleted lines
    inside a <capabilities> block.
    """
    if not text:
        return ContractEffectIR(capabilities_present=False, effect_count=0, effects=[])

    # Strip the outer XML tag if present
    text = re.sub(r'</?capabilities>', '', text)

    effects: list[EffectItem] = []
    
    for line in text.splitlines():
        line = line.strip()
        
        # Skip blank lines and `#` comment lines
        if not line or line.startswith('#'):
            continue
            
        # Iterate bullet lines (lines starting with `-` or `*`)
        if not (line.startswith('-') or line.startswith('*')):
            continue
            
        # Strip the bullet character and leading/trailing whitespace
        content = line[1:].strip()
        
        # Recognize exactly two modals: MAY and MUST NOT
        modal_match = re.match(r'^(MAY|MUST NOT)\b\s+(.*)', content)
        if not modal_match:
            continue
            
        raw_modal = modal_match.group(1)
        remainder = modal_match.group(2).strip()
        
        modal: Literal['MAY', 'MUST_NOT'] = 'MAY' if raw_modal == 'MAY' else 'MUST_NOT'
        
        # Extract action (first word after modal)
        parts = remainder.split(maxsplit=1)
        if not parts:
            continue
            
        action = parts[0].lower()
        
        if len(parts) < 2:
            continue
            
        resource_raw = parts[1]
        
        # Normalize resource
        # Lowercase the phrase
        resource = resource_raw.lower()
        
        # Strip trailing period
        if resource.endswith('.'):
            resource = resource[:-1]
            
        # Split on the first occurrence of `, `, ` or `, or ` and `
        split_segments = re.split(r', | or | and ', resource, maxsplit=1)
        resource = split_segments[0].strip()
        
        # Replace internal spaces with `_`
        resource = resource.replace(' ', '_')
        
        effects.append(EffectItem(
            modal=modal,
            action=action,
            resource=resource
        ))

    # Return default when absent or no parseable bullet lines exist
    if not effects:
        return ContractEffectIR(capabilities_present=False, effect_count=0, effects=[])

    return ContractEffectIR(
        capabilities_present=True,
        effect_count=len(effects),
        effects=effects
    )