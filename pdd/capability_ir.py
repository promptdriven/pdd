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
    """
    if not text:
        return ContractEffectIR(capabilities_present=False, effect_count=0, effects=[])

    # Strip the outer XML tag if present
    tag_match = re.search(r'<capabilities>(.*?)</capabilities>', text, flags=re.DOTALL | re.IGNORECASE)
    if tag_match:
        inner_text = tag_match.group(1)
        capabilities_tag_found = True
    else:
        inner_text = text
        capabilities_tag_found = False

    effects: list[EffectItem] = []
    
    # Bullet regex to capture modal, action, and remainder
    bullet_re = re.compile(r'^\s*[-*]\s+(MAY|MUST NOT)\s+(\S+)\s+(.*)$', re.IGNORECASE)
    
    # Delimiters for resource splitting
    split_re = re.compile(r'(?:,\s+|\s+or\s+|\s+and\s+)')

    for line in inner_text.splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        
        match = bullet_re.match(line)
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
        
        # Resource normalization
        resource_raw = match.group(3).lower()
        if resource_raw.endswith('.'):
            resource_raw = resource_raw[:-1]
            
        resource_raw = resource_raw.strip()
        
        # Split on first occurrence of delimiter and take the first segment
        parts = split_re.split(resource_raw, maxsplit=1)
        resource_primary = parts[0].strip()
        
        # Replace internal spaces with underscores
        resource = re.sub(r'\s+', '_', resource_primary)
        
        effects.append(EffectItem(
            modal=modal,
            action=action,
            resource=resource
        ))
        
    has_effects = len(effects) > 0
    capabilities_present = has_effects

    return ContractEffectIR(
        capabilities_present=capabilities_present,
        effect_count=len(effects),
        effects=effects
    )