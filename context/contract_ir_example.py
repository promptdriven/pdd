import os
import sys
from pathlib import Path
from pprint import pprint

# Add the directory containing the 'pdd' package to sys.path
# This allows importing 'pdd.contract_ir'
PDD_PATH = os.environ.get("PDD_PATH")
if not PDD_PATH:
    print("PDD_PATH environment variable not set. Please set it to the root of the 'pdd' package.")
    sys.exit(0)

sys.path.insert(0, str(Path(PDD_PATH).resolve().parent))

try:
    from pdd.contract_ir import (
        parse_prompt_contracts,
        extract_sections,
        extract_rules,
        extract_waivers,
        iter_covers_refs,
        PromptContractIR,
        Rule,
        Waiver,
        CoversRef,
    )
except ImportError as e:
    print(f"Failed to import from pdd.contract_ir: {e}")
    print("Ensure PDD_PATH is correctly set and the 'pdd' package is accessible.")
    sys.exit(0)


def main() -> None:
    """
    Demonstrates how to use the contract_ir module to parse prompt contract files.
    """
    # Define the output directory for generated files
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True)

    # Define the path for our dummy prompt file
    prompt_filename = "example_contract.prompt"
    prompt_file_path = output_dir / prompt_filename

    # --- 1. Create a dummy .prompt file with various contract sections ---
    prompt_content = """
# This is an example prompt file demonstrating contract sections.

<contract_rules>
R-1: MUST ensure all user input is sanitized before processing.
RULE2a: SHALL NOT expose sensitive data in logs.
3: MAY use caching for frequently accessed data.
* A bullet point rule without an explicit ID.
</contract_rules>

<waivers>
W-001:
  Rule: R-1
  Status: Approved
  Reason: Temporary waiver for initial development phase.
  Approved By: John Doe
  Expires: 2024-12-31

W-002:
  Rule: RULE2a
  Status: Pending
  Reason: Awaiting security review.
  Approved By: Jane Smith
</waivers>

<coverage>
- R-1: Implemented input validation in `src/processor.py`.
- RULE2a: Verified no sensitive data in `log_config.yaml` and `tests/test_logging.py`.
</coverage>

<vocabulary>
- Sanitized: Input that has been processed to remove or neutralize potentially harmful characters or sequences.
- Sensitive Data: Information that requires protection against unauthorized access.
</vocabulary>

<capabilities>
The system can process natural language queries.
</capabilities>

<non_responsibilities>
The system is not responsible for external API uptime.
</non_responsibilities>

<contract_review>
LLM-FINDING-001:
  Rule: R-1
  Status: Open
  Reviewer: Automated LLM
  Reason: Potential edge cases in sanitization logic.
  Date: 2023-10-26
  Assigned To: Dev Team A

LLM-FINDING-002:
  Rule: RULE2a
  Status: Closed
  Reviewer: Security Auditor
  Reason: False positive, logging configuration confirmed secure.
  Date: 2023-10-25
</contract_review>

<formalization>
R-1:
  Level: L1
  Target: input_processor.sanitize_text
  Predicate: is_safe(text)
  Status: Draft

RULE2a:
  Level: L2
  Target: logger.log_message
  Predicate: not contains_sensitive_data(message)
  Status: Proposed
</formalization>

## Covers
- R-1: User Story: Secure Input Handling
- prompts/api/user_profile.prompt#R3: User Story: Profile Data Access
- user_profile.prompt#R4: User Story: Legacy Profile Update (basename match)
- R-1a: User Story: Advanced Sanitization
"""

    print(f"Creating dummy prompt file: {prompt_file_path}")
    prompt_file_path.write_text(prompt_content, encoding="utf-8")

    # --- 2. Parse the prompt file using parse_prompt_contracts ---
    print("\n--- Parsing prompt file ---")
    ir: PromptContractIR = parse_prompt_contracts(prompt_file_path)

    if ir.parse_error:
        print(f"Error parsing prompt file: {ir.parse_error}")
        sys.exit(1)

    print(f"Successfully parsed {ir.path}")
    print(f"IR Version: {ir.version}")
    print(f"Has contract rules: {ir.has_contract_rules}")
    print(f"Has contract sections: {ir.has_contract_sections}")

    # --- 3. Access and print extracted data ---

    print("\n--- Extracted Rules ---")
    for rule in ir.rules:
        print(f"  ID: {rule.raw_id.upper()} (Source Line: {rule.source_line})")
        print(f"    Modal: {rule.modal}")
        print(f"    Is MUST NOT: {rule.is_must_not}")
        print(f"    Terms: {rule.terms}")
        print(f"    Text: {rule.text.splitlines()[0]}...") # Print first line of block
    print(f"Known Rule IDs: {ir.known_rule_ids}")
    print(f"Rule R-1 details: {ir.rule_by_id('R-1')}")
    print(f"Rule R1A details: {ir.rule_by_id('R1A')}") # Demonstrates case-insensitivity and suffix preservation

    print("\n--- Extracted Waivers ---")
    for waiver in ir.waivers:
        print(f"  ID: {waiver.raw_id}")
        print(f"    Rule ID: {waiver.rule_id}")
        print(f"    Status: {waiver.status}")
        print(f"    Expires: {waiver.expires}")
    print(f"Known Waiver IDs: {ir.known_waiver_ids}")

    print("\n--- Extracted Coverage Entries (Rule ID -> Evidence) ---")
    pprint(ir.coverage_entries)

    print("\n--- Extracted Vocabulary Terms ---")
    print(sorted(ir.vocabulary_terms))

    print("\n--- Extracted Review Records ---")
    for review in ir.reviews:
        print(f"  Finding ID: {review.finding_id}")
        print(f"    Rule ID: {review.rule_id}")
        print(f"    Status: {review.status}")
        print(f"    Reviewer: {review.reviewer}")

    print("\n--- Extracted Formalization Records ---")
    for formalization in ir.formalizations:
        print(f"  Rule ID: {formalization.rule_id}")
        print(f"    Level: {formalization.level}")
        print(f"    Target: {formalization.target}")
        print(f"    Status: {formalization.status}")

    print("\n--- Story Covers (from ## Covers section) ---")
    # Note: iter_covers_refs is used internally by rule_ids_from_covers
    # We can demonstrate it directly with the raw section text.
    covers_section_text = ir.sections.get("covers", "")
    if covers_section_text:
        print("Raw Covers section text:")
        print(covers_section_text)
        print("\nParsed Covers References:")
        covers_refs: list[CoversRef] = iter_covers_refs(covers_section_text)
        for ref in covers_refs:
            print(f"  Rule ID: {ref.rule_id}, Prompt Filename: {ref.prompt_filename}, Line: '{ref.line}'")

    # --- 4. Demonstrate helper functions with raw text ---
    print("\n--- Demonstrating extract_sections with raw text ---")
    raw_text = "<foo>bar</foo>\n## My Heading\nContent under heading."
    sections = extract_sections(raw_text)
    pprint(sections)

    print("\n--- Demonstrating extract_rules with raw text ---")
    raw_rules_text = """
R-10: MUST be secure.
  This is a multi-line rule.

20: SHALL be fast.
"""
    rules: list[Rule] = extract_rules(raw_rules_text)
    for rule in rules:
        print(f"  ID: {rule.raw_id}, Modal: {rule.modal}, Text: {rule.block.splitlines()[0]}...")

    print("\n--- Demonstrating extract_waivers with raw text ---")
    raw_waivers_text = """
W-999:
  Rule: R-10
  Status: Active
  Reason: Test waiver.
"""
    waivers: list[Waiver] = extract_waivers(raw_waivers_text)
    for waiver in waivers:
        print(f"  ID: {waiver.raw_id}, Rule ID: {waiver.rule_id}, Status: {waiver.status}")

    # --- 5. Demonstrate as_dict() for JSON-safe representation ---
    print("\n--- PromptContractIR as_dict() representation (partial output) ---")
    ir_dict = ir.as_dict()
    # Print only a few keys to keep output concise
    print(f"Version: {ir_dict.get('version')}")
    print(f"Path: {ir_dict.get('path')}")
    print(f"Number of rules in dict: {len(ir_dict.get('rules', []))}")
    if ir_dict.get('rules'):
        print("First rule in dict:")
        pprint(ir_dict['rules'][0])
    print(f"Vocabulary terms in dict: {ir_dict.get('vocabulary')[:3]}...") # Show first 3
    print(f"Number of waivers in dict: {len(ir_dict.get('waivers', []))}")


if __name__ == "__main__":
    main()
