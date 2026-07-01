"""
Example usage of pdd.capability_ir.

Demonstrates how to parse a <capabilities> block (or plain inner text) into
a ContractEffectIR containing a list of EffectItem entries.

Functions:
    parse_capabilities_ir(text: str) -> ContractEffectIR
        - text: raw string, either the full <capabilities>...</capabilities>
                XML block or its inner text
        - returns: ContractEffectIR with fields:
            capabilities_present (bool): True when at least one effect was parsed
            effect_count (int): number of parsed EffectItem entries
            effects (list[EffectItem]): parsed items, each with:
                modal (Literal['MAY', 'MUST_NOT'])
                action (str): lowercased verb
                resource (str): normalized snake_case noun phrase
"""

import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.capability_ir import parse_capabilities_ir, EffectItem, ContractEffectIR

# ---------------------------------------------------------------------------
# Example 1: Full <capabilities> block with canonical capability phrasing
# ---------------------------------------------------------------------------
full_block = """<capabilities>
- MAY read payment records.
- MAY write refund records.
- MAY call the payment provider refund endpoint.
- MAY write audit events.
- MUST NOT send emails.
- MUST NOT log provider secrets, bearer tokens, card PAN, or CVV.
</capabilities>"""

result1 = parse_capabilities_ir(full_block)
print("=== Example 1: Full <capabilities> block ===")
print(f"capabilities_present : {result1.capabilities_present}")
print(f"effect_count         : {result1.effect_count}")
for item in result1.effects:
    print(f"  EffectItem(modal={item.modal!r}, action={item.action!r}, resource={item.resource!r})")
print()

assert result1.capabilities_present is True
assert result1.effect_count == 6
assert result1.effects[0] == EffectItem(modal='MAY', action='read', resource='payment_records')
assert result1.effects[1] == EffectItem(modal='MAY', action='write', resource='refund_records')
assert result1.effects[2] == EffectItem(modal='MAY', action='call', resource='payment_provider_refund_endpoint')
assert result1.effects[3] == EffectItem(modal='MAY', action='write', resource='audit_events')
assert result1.effects[4] == EffectItem(modal='MUST_NOT', action='send', resource='email')
assert result1.effects[5] == EffectItem(modal='MUST_NOT', action='log', resource='secrets')

# ---------------------------------------------------------------------------
# Example 2: Plain inner text (no XML wrapper)
# ---------------------------------------------------------------------------
inner_text = """
- MAY log user_activity
- MUST NOT access admin_panel
"""

result2 = parse_capabilities_ir(inner_text)
print("=== Example 2: Plain inner text (no XML wrapper) ===")
print(f"capabilities_present : {result2.capabilities_present}")
print(f"effect_count         : {result2.effect_count}")
for item in result2.effects:
    print(f"  EffectItem(modal={item.modal!r}, action={item.action!r}, resource={item.resource!r})")
print()

assert result2.capabilities_present is True
assert result2.effect_count == 2
assert result2.effects[0] == EffectItem(modal='MAY', action='log', resource='user_activity')
assert result2.effects[1] == EffectItem(modal='MUST_NOT', action='access', resource='admin_panel')

# ---------------------------------------------------------------------------
# Example 3: Resource normalization — trailing period, `, `, ` or `, ` and `
# ---------------------------------------------------------------------------
normalization_block = """<capabilities>
- MAY read payment records, invoices, or receipts.
- MUST NOT send email or sms
- MAY call database and cache
* MAY write temp_files
</capabilities>"""

result3 = parse_capabilities_ir(normalization_block)
print("=== Example 3: Resource normalization ===")
print(f"capabilities_present : {result3.capabilities_present}")
print(f"effect_count         : {result3.effect_count}")
for item in result3.effects:
    print(f"  EffectItem(modal={item.modal!r}, action={item.action!r}, resource={item.resource!r})")
print()

assert result3.capabilities_present is True
assert result3.effect_count == 4
# trailing period stripped, `, ` splits → first segment only
assert result3.effects[0].resource == 'payment_records'
# ` or ` splits → first segment only
assert result3.effects[1].resource == 'email'
# ` and ` splits → first segment only
assert result3.effects[2].resource == 'database'
# asterisk bullet works
assert result3.effects[3].resource == 'temp_files'

# ---------------------------------------------------------------------------
# Example 4: Empty / no-bullet / full prompt without tag → capabilities_present=False
# ---------------------------------------------------------------------------
result4a = parse_capabilities_ir("")
print("=== Example 4a: Empty string ===")
print(f"capabilities_present : {result4a.capabilities_present}")
print(f"effect_count         : {result4a.effect_count}")
print()
assert result4a == ContractEffectIR(capabilities_present=False, effect_count=0, effects=[])

no_bullets = "<capabilities>\n# just a comment\n</capabilities>"
result4b = parse_capabilities_ir(no_bullets)
print("=== Example 4b: Tag present but no bullets ===")
print(f"capabilities_present : {result4b.capabilities_present}")
print(f"effect_count         : {result4b.effect_count}")
print()
assert result4b == ContractEffectIR(capabilities_present=False, effect_count=0, effects=[])

full_prompt_without_tag = """# Refund module

## Requirements
- MAY read payment records.
- MUST NOT send emails.
"""
result4c = parse_capabilities_ir(full_prompt_without_tag)
print("=== Example 4c: Full prompt without <capabilities> tag ===")
print(f"capabilities_present : {result4c.capabilities_present}")
print(f"effect_count         : {result4c.effect_count}")
print()
assert result4c == ContractEffectIR(capabilities_present=False, effect_count=0, effects=[])

# ---------------------------------------------------------------------------
# Example 5: Unrecognized modal silently skipped
# ---------------------------------------------------------------------------
unrecognized_block = """<capabilities>
- SHOULD read logs
- MAY write audit_trail
</capabilities>"""

result5 = parse_capabilities_ir(unrecognized_block)
print("=== Example 5: Unrecognized modal skipped ===")
print(f"capabilities_present : {result5.capabilities_present}")
print(f"effect_count         : {result5.effect_count}")
for item in result5.effects:
    print(f"  EffectItem(modal={item.modal!r}, action={item.action!r}, resource={item.resource!r})")
print()

assert result5.capabilities_present is True
assert result5.effect_count == 1
assert result5.effects[0] == EffectItem(modal='MAY', action='write', resource='audit_trail')

print("All examples ran successfully.")
