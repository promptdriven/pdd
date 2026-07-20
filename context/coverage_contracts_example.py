import os
import sys
import textwrap
from pathlib import Path

# CRITICAL: The PDD_PATH environment variable is set to the path of the pdd directory.
# We need to add it to sys.path to import modules from the pdd package.
pdd_path = os.environ.get("PDD_PATH")
if not pdd_path:
    print("PDD_PATH environment variable not set. Please set it to the root of the 'pdd' package.")
    sys.exit(0)

sys.path.insert(0, str(Path(pdd_path).resolve().parent))

from pdd.coverage_contracts import (  # noqa: E402
    CoverageResult,
    build_coverage,
    build_coverage_directory,
)

def create_dummy_files(base_dir: Path):
    """
    Creates a dummy project structure with prompt, story, and test files
    to demonstrate coverage analysis.
    """
    print(f"Creating dummy files in: {base_dir.resolve()}")

    prompts_dir = base_dir / "prompts"
    stories_dir = base_dir / "user_stories"
    tests_dir = base_dir / "tests"

    prompts_dir.mkdir(parents=True, exist_ok=True)
    stories_dir.mkdir(parents=True, exist_ok=True)
    tests_dir.mkdir(parents=True, exist_ok=True)

    # --- Prompt 1: example.prompt ---
    prompt_content_1 = textwrap.dedent("""
    # Example Prompt
    This is an example prompt demonstrating contract rules and coverage.

    <contract_rules>
    R1 - Rule checked by story and test.
    R2 - Rule covered by story only.
    R3 - Rule covered by test only.
    R4 - Rule that is explicitly waived.
    R5 - Rule that is unchecked.
    R6 - Rule with a story that has no Acceptance Criteria (failed evidence).
    R7 - Rule covered by a cross-unit story.
    </contract_rules>

    <coverage>
    R1: story__example_r1.md, test_R1_feature
    R4: WAIVED W1
    </coverage>

    <waivers>
    W1: R4 - This rule is temporarily waived. Expires 2099-12-31.
    </waivers>
    """)
    (prompts_dir / "example.prompt").write_text(prompt_content_1)

    # --- Prompt 2: sub/another.prompt (for directory scan and qualified tests) ---
    (prompts_dir / "sub").mkdir(exist_ok=True)
    prompt_content_2 = textwrap.dedent("""
    # Another Prompt
    This prompt is in a subdirectory and uses qualified test references.

    <contract_rules>
    R10 - Rule checked by a qualified test.
    R11 - Rule covered by a cross-unit story (already counted globally).
    </contract_rules>
    """)
    (prompts_dir / "sub" / "another.prompt").write_text(prompt_content_2)

    # --- Story 1: story__example_r1.md ---
    story_content_1 = textwrap.dedent("""
    # Story for R1
    This story covers R1.

    ## Covers
    R1

    ## Acceptance Criteria
    - The system must satisfy R1.
    """)
    (stories_dir / "story__example_r1.md").write_text(story_content_1)

    # --- Story 2: story__example_r2.md (for R2 and R6 failure) ---
    story_content_2 = textwrap.dedent("""
    # Story for R2 and R6
    This story covers R2 and R6.

    ## Covers
    R2
    R6
    """) # Missing Acceptance Criteria for R6 failure
    (stories_dir / "story__example_r2.md").write_text(story_content_2)

    # --- Story 3: story__cross_unit.md (for R7 and R11) ---
    story_content_3 = textwrap.dedent("""
    <!-- pdd-story-dev-units: unit_a, unit_b -->
    <!-- pdd-story-prompts: example.prompt, sub/another.prompt -->
    # Cross-Unit Story
    This story covers R7 in example.prompt and R11 in sub/another.prompt.

    ## Covers
    example.prompt#R7
    sub/another.prompt#R11

    ## Acceptance Criteria
    - This story is cross-unit.
    """)
    (stories_dir / "story__cross_unit.md").write_text(story_content_3)

    # --- Test 1: test_example.py ---
    test_content_1 = textwrap.dedent("""
    import pytest

    def test_R1_feature():
        # Tests R1 functionality.
        assert True

    def test_R3_logic():
        # covers R3
        assert True

    @pytest.mark.story(story_id="example_r1")
    def test_story_example_r1_regression():
        assert True
    """)
    (tests_dir / "test_example.py").write_text(test_content_1)

    # --- Test 2: test_sub_another.py (for qualified reference) ---
    test_content_2 = textwrap.dedent("""
    import pytest

    def test_qualified_rule_10():
        # Covers prompts/sub/another.prompt#R10
        assert True

    @pytest.mark.story(story_id="cross_unit")
    def test_story_cross_unit_regression():
        assert True
    """)
    (tests_dir / "test_sub_another.py").write_text(test_content_2)

    # --- Test 3: test_syntax_error.py (for test validation failure) ---
    test_content_3 = textwrap.dedent("""
    # This file has a syntax error and references R5
    def test_syntax_error_rule_5():
        # covers R5
        if True:
            pass
        else
            fail_syntax
    """)
    (tests_dir / "test_syntax_error.py").write_text(test_content_3)


def main():
    """
    Demonstrates how to use build_coverage and build_coverage_directory.
    """
    # Define an output directory relative to the script's location
    script_dir = Path(__file__).parent
    output_dir = script_dir / "output" / "coverage_contracts_example"
    output_dir.mkdir(parents=True, exist_ok=True)

    # Create dummy files for the example
    create_dummy_files(output_dir)

    prompts_dir = output_dir / "prompts"
    stories_dir = output_dir / "user_stories"
    tests_dir = output_dir / "tests"
    project_root = output_dir # Treat the output_dir as the project root for path resolution

    print("\n--- Demonstrating build_coverage for a single prompt file ---")
    example_prompt_path = prompts_dir / "example.prompt"
    print(f"Analyzing: {example_prompt_path.relative_to(output_dir)}")

    # Build coverage for a single prompt
    # Note: global_story_registry is None here, so no deduplication occurs.
    single_file_result: CoverageResult = build_coverage(
        path=example_prompt_path,
        stories_dir=stories_dir,
        tests_dir=tests_dir,
        project_root=project_root,
    )

    if single_file_result.error:
        print(f"Error building coverage: {single_file_result.error}")
    else:
        print("\nCoverage Result (example.prompt):")
        print(f"  Has contract rules: {single_file_result.has_contract_rules}")
        print(f"  Read errors: {single_file_result.read_errors}")
        print(f"  Summary: {single_file_result.summary}")
        print("  Rules:")
        for rule in single_file_result.rules:
            print(f"    - {rule.rule_id}: Status={rule.status}, Stories={rule.stories}, "
                  f"Tests={rule.tests}, Waiver={rule.waiver}, Waiver Status={rule.waiver_status}, "
                  f"Failures={rule.failures}, Is Cross-Unit={rule.is_cross_unit}, "
                  f"Partners={rule.cross_unit_partners}")
        print("  Stories (Regression Status):")
        for story_reg in single_file_result.stories:
            print(f"    - {story_reg.story_id}: Has Regression Test={story_reg.has_regression_test}, "
                  f"Status={story_reg.status}, Tests={story_reg.tests}, Hash={story_reg.story_hash}")
        print(f"  Cross-unit stories linked to this prompt: {single_file_result.cross_unit_stories}")
        print(f"  Regression warnings: {single_file_result.regression_warnings}")

    print("\n--- Demonstrating build_coverage_directory for all prompt files ---")
    print(f"Analyzing all prompts in: {prompts_dir.relative_to(output_dir)}")

    # Build coverage for all prompts in a directory
    # This will use require_prompt_qualified_tests=True and handle global story deduplication.
    directory_results: list[CoverageResult] = build_coverage_directory(
        directory=prompts_dir,
        stories_dir=stories_dir,
        tests_dir=tests_dir,
        project_root=project_root,
    )

    print("\nCoverage Results (Directory Scan):")
    for result in directory_results:
        print(f"\nFile: {result.path.relative_to(output_dir)}")
        if result.error:
            print(f"  Error: {result.error}")
            continue
        print(f"  Has contract rules: {result.has_contract_rules}")
        print(f"  Read errors: {result.read_errors}")
        print(f"  Summary: {result.summary}")
        print("  Rules:")
        for rule in result.rules:
            print(f"    - {rule.rule_id}: Status={rule.status}, Stories={rule.stories}, "
                  f"Tests={rule.tests}, Waiver={rule.waiver}, Waiver Status={rule.waiver_status}, "
                  f"Failures={rule.failures}, Is Cross-Unit={rule.is_cross_unit}, "
                  f"Partners={rule.cross_unit_partners}")
        print("  Stories (Regression Status):")
        for story_reg in result.stories:
            print(f"    - {story_reg.story_id}: Has Regression Test={story_reg.has_regression_test}, "
                  f"Status={story_reg.status}, Tests={story_reg.tests}, Hash={story_reg.story_hash}")
        print(f"  Cross-unit stories linked to this prompt: {result.cross_unit_stories}")
        print(f"  Regression warnings: {result.regression_warnings}")

    print(f"\nExample finished. Check '{output_dir.resolve()}' for generated files.")

if __name__ == "__main__":
    main()
