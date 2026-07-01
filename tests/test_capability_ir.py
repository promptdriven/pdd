"""
Test plan for pdd.capability_ir
=================================

Requirements from spec:
 R1.  EffectItem is a frozen dataclass with modal, action, resource fields
 R2.  ContractEffectIR is a dataclass with capabilities_present, effect_count, effects fields
 R3.  parse_capabilities_ir(text: str) -> ContractEffectIR is exposed at module level
 R4.  Accepts the full <capabilities>...</capabilities> XML block
 R5.  Accepts plain inner text (no XML wrapper) — "or its inner text"
 R6.  Strips the outer XML tag before processing
 R7.  Iterates bullet lines starting with `-`
 R8.  Iterates bullet lines starting with `*`
 R9.  Skips blank lines
 R10. Skips `#` comment lines
 R11. Recognizes `MAY` modal → 'MAY'
 R12. Recognizes `MUST NOT` modal → 'MUST_NOT'
 R13. Silently skips lines with unrecognized modals
 R14. Extracts first word after modal as action (lowercased)
 R15. Resource: lowercases the phrase
 R16. Resource: strips trailing period
 R17. Resource: splits on `, ` (comma-space), takes first segment
 R18. Resource: splits on ` or `, takes first segment
 R19. Resource: splits on ` and `, takes first segment
 R20. Resource: replaces internal spaces with `_`
 R21. Returns ContractEffectIR(False, 0, []) on empty input
 R22. Returns ContractEffectIR(False, 0, []) when no parseable bullets found
 R23. Sets capabilities_present=True when at least one bullet parsed
 R24. Sets effect_count=len(effects) accurately
 R25. Only stdlib imports (re, dataclasses, typing) — no ast, pylint, or code-analysis libs
 R26. Exports EffectItem, ContractEffectIR, parse_capabilities_ir at module level
 R27. Full prompts without a <capabilities> tag return the false/empty sentinel
 R28. Canonical capability examples normalize common semantic resources predictably

Regression tests:
 RG1. Non-bullet lines (no leading - or *) are skipped
 RG2. Lines with bullets but no matching modal are skipped (action-only lines)
 RG3. Multiple split-pattern types in one run all work independently
"""

import pytest
from pdd.capability_ir import parse_capabilities_ir, EffectItem, ContractEffectIR


# ---------------------------------------------------------------------------
# R1/R2: Data model shape
# ---------------------------------------------------------------------------

class TestDataModels:
    def test_effect_item_is_frozen(self):
        """R1: EffectItem must be frozen (immutable)."""
        item = EffectItem(modal='MAY', action='read', resource='logs')
        with pytest.raises((AttributeError, TypeError)):
            item.action = 'write'  # type: ignore[misc]

    def test_effect_item_fields(self):
        """R1: EffectItem has modal, action, resource."""
        item = EffectItem(modal='MUST_NOT', action='send', resource='email')
        assert item.modal == 'MUST_NOT'
        assert item.action == 'send'
        assert item.resource == 'email'

    def test_contract_effect_ir_fields(self):
        """R2: ContractEffectIR has capabilities_present, effect_count, effects."""
        ir = ContractEffectIR(capabilities_present=True, effect_count=1,
                              effects=[EffectItem(modal='MAY', action='log', resource='events')])
        assert ir.capabilities_present is True
        assert ir.effect_count == 1
        assert len(ir.effects) == 1

    def test_contract_effect_ir_is_mutable(self):
        """R2: ContractEffectIR is not frozen — can be mutated."""
        ir = ContractEffectIR(capabilities_present=False, effect_count=0, effects=[])
        ir.effect_count = 5
        assert ir.effect_count == 5


# ---------------------------------------------------------------------------
# R3/R26: Module-level exports
# ---------------------------------------------------------------------------

class TestModuleExports:
    def test_exports_effect_item(self):
        """R26: EffectItem is exported at module level."""
        import pdd.capability_ir as m
        assert hasattr(m, 'EffectItem')

    def test_exports_contract_effect_ir(self):
        """R26: ContractEffectIR is exported at module level."""
        import pdd.capability_ir as m
        assert hasattr(m, 'ContractEffectIR')

    def test_exports_parse_capabilities_ir(self):
        """R26/R3: parse_capabilities_ir is exported at module level."""
        import pdd.capability_ir as m
        assert callable(m.parse_capabilities_ir)


# ---------------------------------------------------------------------------
# R4: Accepts full XML block
# ---------------------------------------------------------------------------

class TestAcceptsXMLBlock:
    def test_full_xml_block_parsed(self):
        """R4: Full <capabilities>...</capabilities> block is accepted."""
        text = "<capabilities>\n- MAY read logs\n</capabilities>"
        result = parse_capabilities_ir(text)
        assert result.capabilities_present is True
        assert result.effect_count == 1
        assert result.effects[0] == EffectItem(modal='MAY', action='read', resource='logs')

    def test_xml_block_multiline(self):
        """R4: Multiple bullets inside full XML block."""
        text = "<capabilities>\n- MAY write cache\n- MUST NOT delete records\n</capabilities>"
        result = parse_capabilities_ir(text)
        assert result.effect_count == 2


# ---------------------------------------------------------------------------
# R5: Accepts plain inner text (no XML wrapper)
# ---------------------------------------------------------------------------

class TestAcceptsPlainText:
    def test_plain_text_without_tags(self):
        """R5: Plain bullet text without XML tags is accepted."""
        text = "- MAY read config"
        result = parse_capabilities_ir(text)
        assert result.capabilities_present is True
        assert result.effect_count == 1
        assert result.effects[0].action == 'read'
        assert result.effects[0].resource == 'config'

    def test_plain_multiline_text(self):
        """R5: Multiple bullet lines without XML wrapper."""
        text = "- MAY send notifications\n- MUST NOT access secrets"
        result = parse_capabilities_ir(text)
        assert result.effect_count == 2

    def test_plain_text_with_unknown_modal_still_skips_line(self):
        """R5/R13: Tagless inner bullet text can still skip unknown modals."""
        text = "- SHOULD log events\n- MAY read logs"
        result = parse_capabilities_ir(text)
        assert result.effect_count == 1
        assert result.effects[0] == EffectItem(modal='MAY', action='read', resource='logs')


# ---------------------------------------------------------------------------
# R6: Strips outer XML tag
# ---------------------------------------------------------------------------

class TestStripsXMLTag:
    def test_xml_tag_stripped(self):
        """R6: The <capabilities> and </capabilities> tags are stripped."""
        text = "<capabilities>- MAY read files</capabilities>"
        result = parse_capabilities_ir(text)
        assert result.capabilities_present is True
        assert result.effects[0].resource == 'files'


# ---------------------------------------------------------------------------
# R7/R8: Bullet characters
# ---------------------------------------------------------------------------

class TestBulletCharacters:
    def test_dash_bullet(self):
        """R7: Lines starting with `-` are parsed."""
        result = parse_capabilities_ir("- MAY read logs")
        assert result.effect_count == 1

    def test_asterisk_bullet(self):
        """R8: Lines starting with `*` are parsed."""
        result = parse_capabilities_ir("* MAY write output")
        assert result.effect_count == 1
        assert result.effects[0].action == 'write'

    def test_non_bullet_line_skipped(self):
        """RG1: Lines without leading - or * are skipped."""
        text = "MAY read logs"
        result = parse_capabilities_ir(text)
        assert result.capabilities_present is False
        assert result.effect_count == 0


# ---------------------------------------------------------------------------
# R9/R10: Skip blank and comment lines
# ---------------------------------------------------------------------------

class TestSkipLines:
    def test_skips_blank_lines(self):
        """R9: Blank lines are ignored."""
        text = "\n\n- MAY read config\n\n"
        result = parse_capabilities_ir(text)
        assert result.effect_count == 1

    def test_skips_comment_lines(self):
        """R10: Lines starting with # are skipped."""
        text = "# this is a comment\n- MAY read logs"
        result = parse_capabilities_ir(text)
        assert result.effect_count == 1
        assert result.effects[0].action == 'read'

    def test_only_comments_gives_no_effects(self):
        """R10/R22: Only comment lines → capabilities_present=False."""
        text = "<capabilities>\n# comment only\n</capabilities>"
        result = parse_capabilities_ir(text)
        assert result.capabilities_present is False


# ---------------------------------------------------------------------------
# R11/R12: Modal recognition
# ---------------------------------------------------------------------------

class TestModalRecognition:
    def test_may_modal(self):
        """R11: MAY maps to 'MAY'."""
        result = parse_capabilities_ir("- MAY read logs")
        assert result.effects[0].modal == 'MAY'

    def test_must_not_modal(self):
        """R12: MUST NOT maps to 'MUST_NOT'."""
        result = parse_capabilities_ir("- MUST NOT write secrets")
        assert result.effects[0].modal == 'MUST_NOT'


# ---------------------------------------------------------------------------
# R13: Silently skips unrecognized modals
# ---------------------------------------------------------------------------

class TestUnrecognizedModal:
    def test_unknown_modal_skipped(self):
        """R13: Unrecognized modals like SHOULD, CAN are silently skipped."""
        text = "- SHOULD read logs\n- MAY write audit"
        result = parse_capabilities_ir(text)
        assert result.effect_count == 1
        assert result.effects[0].modal == 'MAY'

    def test_all_unknown_modals_skipped(self):
        """R13: All lines with unrecognized modals → capabilities_present=False."""
        text = "- COULD read files\n- MIGHT write output"
        result = parse_capabilities_ir(text)
        assert result.capabilities_present is False
        assert result.effect_count == 0


# ---------------------------------------------------------------------------
# R14: Action extraction (first word after modal, lowercased)
# ---------------------------------------------------------------------------

class TestActionExtraction:
    def test_action_lowercased(self):
        """R14: Action is the first word after modal, lowercased."""
        result = parse_capabilities_ir("- MAY READ logs")
        assert result.effects[0].action == 'read'

    def test_action_from_must_not(self):
        """R14: Action extracted correctly after MUST NOT."""
        result = parse_capabilities_ir("- MUST NOT WRITE secrets")
        assert result.effects[0].action == 'write'

    def test_various_actions(self):
        """R14: Various verbs are extracted correctly."""
        text = "- MAY call external_api\n- MAY send email\n- MAY log events"
        result = parse_capabilities_ir(text)
        actions = [e.action for e in result.effects]
        assert actions == ['call', 'send', 'log']


# ---------------------------------------------------------------------------
# R15-R20: Resource normalization
# ---------------------------------------------------------------------------

class TestResourceNormalization:
    def test_resource_lowercased(self):
        """R15: Resource is lowercased."""
        result = parse_capabilities_ir("- MAY read PaymentRecords")
        assert result.effects[0].resource == 'paymentrecords'

    def test_resource_trailing_period_stripped(self):
        """R16: Trailing period is removed from resource."""
        result = parse_capabilities_ir("- MAY read logs.")
        assert result.effects[0].resource == 'logs'

    def test_resource_comma_space_split(self):
        """R17: `, ` splits resource — only first segment kept."""
        result = parse_capabilities_ir("- MAY read payment records, invoices, receipts")
        assert result.effects[0].resource == 'payment_records'

    def test_resource_or_split(self):
        """R18: ` or ` splits resource — only first segment kept."""
        result = parse_capabilities_ir("- MUST NOT send email or sms")
        assert result.effects[0].resource == 'email'

    def test_resource_and_split(self):
        """R19: ` and ` splits resource — only first segment kept."""
        result = parse_capabilities_ir("- MAY call database and cache")
        assert result.effects[0].resource == 'database'

    def test_resource_spaces_replaced_with_underscore(self):
        """R20: Internal spaces in resource replaced with `_`."""
        result = parse_capabilities_ir("- MAY read payment records")
        assert result.effects[0].resource == 'payment_records'

    def test_resource_period_then_split(self):
        """R16+R17: Trailing period stripped before splitting."""
        result = parse_capabilities_ir("- MAY read payment records, invoices.")
        # trailing period stripped first, then comma split
        assert result.effects[0].resource == 'payment_records'

    def test_resource_multi_word_no_split_needed(self):
        """R20: Multi-word resource with no split markers → spaces become underscores."""
        result = parse_capabilities_ir("- MAY write temp file storage")
        assert result.effects[0].resource == 'temp_file_storage'

    def test_resource_leading_article_stripped(self):
        """R28: Leading articles do not become part of the normalized resource."""
        result = parse_capabilities_ir("- MAY call the payment provider refund endpoint")
        assert result.effects[0].resource == 'payment_provider_refund_endpoint'

    def test_resource_plural_email_normalized(self):
        """R28: Email/email plural variants normalize to the semantic email resource."""
        result = parse_capabilities_ir("- MUST NOT send emails.")
        assert result.effects[0] == EffectItem(modal='MUST_NOT', action='send', resource='email')

    def test_resource_provider_secrets_normalized(self):
        """R28: Compound secret phrases normalize to the semantic secrets resource."""
        result = parse_capabilities_ir("- MUST NOT log provider secrets, bearer tokens, card PAN, or CVV.")
        assert result.effects[0] == EffectItem(modal='MUST_NOT', action='log', resource='secrets')


# ---------------------------------------------------------------------------
# R21/R22: Empty / no-bullets → capabilities_present=False
# ---------------------------------------------------------------------------

class TestEmptyAndNoBullets:
    def test_empty_string(self):
        """R21: Empty string → ContractEffectIR(False, 0, [])."""
        result = parse_capabilities_ir("")
        assert result == ContractEffectIR(capabilities_present=False, effect_count=0, effects=[])

    def test_only_whitespace(self):
        """R21: Whitespace-only input → capabilities_present=False."""
        result = parse_capabilities_ir("   \n\n  ")
        assert result.capabilities_present is False
        assert result.effect_count == 0

    def test_tag_with_no_bullets(self):
        """R22: <capabilities> tag present but inner text has no bullets."""
        result = parse_capabilities_ir("<capabilities>\n# comment\n</capabilities>")
        assert result == ContractEffectIR(capabilities_present=False, effect_count=0, effects=[])

    def test_tag_with_only_non_bullet_lines(self):
        """R22: Non-bullet lines only → no effects."""
        result = parse_capabilities_ir("<capabilities>\nsome text\n</capabilities>")
        assert result.capabilities_present is False

    def test_full_prompt_without_capabilities_tag_ignored(self):
        """R27: Full prompts without the capabilities tag are not parsed as inner text."""
        text = """# Refund module

## Requirements
- MAY read payment records.
- MUST NOT send emails.
"""
        result = parse_capabilities_ir(text)
        assert result == ContractEffectIR(capabilities_present=False, effect_count=0, effects=[])


# ---------------------------------------------------------------------------
# R23/R24: capabilities_present and effect_count set correctly
# ---------------------------------------------------------------------------

class TestCapabilitiesPresentAndCount:
    def test_capabilities_present_true_when_effects(self):
        """R23: capabilities_present=True when at least one bullet parsed."""
        result = parse_capabilities_ir("- MAY read logs")
        assert result.capabilities_present is True

    def test_effect_count_matches_effects_length(self):
        """R24: effect_count == len(effects)."""
        text = "- MAY read logs\n- MAY write output\n- MUST NOT delete records"
        result = parse_capabilities_ir(text)
        assert result.effect_count == len(result.effects)
        assert result.effect_count == 3

    def test_effect_count_with_skipped_lines(self):
        """R24: effect_count reflects only successfully parsed bullets."""
        text = "- MAY read logs\n- SHOULD write stuff\n# comment\n- MUST NOT access secrets"
        result = parse_capabilities_ir(text)
        assert result.effect_count == 2  # SHOULD is skipped


# ---------------------------------------------------------------------------
# R25: No forbidden imports
# ---------------------------------------------------------------------------

class TestNoForbiddenImports:
    def test_no_ast_import(self):
        """R25: `ast` module must NOT be imported."""
        import pdd.capability_ir as m
        import sys
        # The module should not have imported ast
        source_path = m.__file__
        with open(source_path) as f:
            source = f.read()
        assert 'import ast' not in source

    def test_no_pylint_import(self):
        """R25: `pylint` must NOT be imported."""
        import pdd.capability_ir as m
        source_path = m.__file__
        with open(source_path) as f:
            source = f.read()
        assert 'import pylint' not in source


# ---------------------------------------------------------------------------
# RG2: Regression — bullet with no matching modal is skipped
# ---------------------------------------------------------------------------

class TestRegressions:
    def test_bullet_with_no_modal_skipped(self):
        """RG2: A bullet line that has no MAY/MUST NOT modal is silently skipped."""
        text = "- read logs\n- MAY write output"
        result = parse_capabilities_ir(text)
        assert result.effect_count == 1
        assert result.effects[0].action == 'write'

    def test_mixed_bullet_types(self):
        """R7+R8: Mix of - and * bullets both parsed."""
        text = "- MAY read config\n* MUST NOT write secrets"
        result = parse_capabilities_ir(text)
        assert result.effect_count == 2
        assert result.effects[0].modal == 'MAY'
        assert result.effects[1].modal == 'MUST_NOT'

    def test_full_integration(self):
        """Integration: realistic capabilities block end-to-end."""
        text = """<capabilities>
# This contract governs data access
- MAY read payment_records
- MAY send email
- MUST NOT write secrets
- MUST NOT call external_api
- SHOULD log events
</capabilities>"""
        result = parse_capabilities_ir(text)
        assert result.capabilities_present is True
        assert result.effect_count == 4  # SHOULD skipped
        assert result.effects[0] == EffectItem(modal='MAY', action='read', resource='payment_records')
        assert result.effects[1] == EffectItem(modal='MAY', action='send', resource='email')
        assert result.effects[2] == EffectItem(modal='MUST_NOT', action='write', resource='secrets')
        assert result.effects[3] == EffectItem(modal='MUST_NOT', action='call', resource='external_api')

    def test_epic_capabilities_sample_normalizes_expected_resources(self):
        """R28: The epic's canonical sample produces stable target-neutral resources."""
        text = """<capabilities>
- MAY read payment records.
- MAY write refund records.
- MAY call the payment provider refund endpoint.
- MAY write audit events.
- MUST NOT send emails.
- MUST NOT modify customer profile records.
- MUST NOT read unrelated environment variables.
- MUST NOT log provider secrets, bearer tokens, card PAN, or CVV.
</capabilities>"""
        result = parse_capabilities_ir(text)
        assert result.capabilities_present is True
        assert result.effect_count == 8
        assert result.effects == [
            EffectItem(modal='MAY', action='read', resource='payment_records'),
            EffectItem(modal='MAY', action='write', resource='refund_records'),
            EffectItem(modal='MAY', action='call', resource='payment_provider_refund_endpoint'),
            EffectItem(modal='MAY', action='write', resource='audit_events'),
            EffectItem(modal='MUST_NOT', action='send', resource='email'),
            EffectItem(modal='MUST_NOT', action='modify', resource='customer_profile_records'),
            EffectItem(modal='MUST_NOT', action='read', resource='unrelated_environment_variables'),
            EffectItem(modal='MUST_NOT', action='log', resource='secrets'),
        ]
