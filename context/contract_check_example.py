import sys
from pathlib import Path

# --- Path Setup for Module Import ---
# Get the directory of the current script (contract_check_example.py)
current_script_dir = Path(__file__).parent

# Assuming 'pdd' directory is one level up from 'context'
# and then inside 'pdd' is 'contract_check.py'
# This adds the parent directory of 'pdd' to sys.path, allowing 'from pdd import contract_check'
pdd_package_root = current_script_dir.parent
sys.path.insert(0, str(pdd_package_root))

# Now import the module
from pdd import contract_check  # noqa: E402

# --- Output Directory Setup ---
# All created files (e.g., output files, prompt files, etc.) will be in the './output' directory.
output_dir = current_script_dir / "output"
output_dir.mkdir(exist_ok=True)

print(f"Using output directory: {output_dir.resolve()}")

# --- Helper to create dummy files ---
def create_dummy_file(filepath: Path, content: str):
    """Creates a dummy file with the given content."""
    filepath.parent.mkdir(parents=True, exist_ok=True)
    filepath.write_text(content, encoding="utf-8")
    print(f"Created dummy file: {filepath.relative_to(output_dir)}")

# --- 1. Example for check_prompt ---
print("\n--- Running check_prompt example ---")

# Create a dummy prompt file with various contract sections
prompt_content_single = """
# My Service Contract

<contract_rules>
R1: The system MUST process payments within 5 seconds.
R2: The system MUST NOT store full credit card numbers.
R3: The system SHOULD log all successful transactions.
R4: The system MUST handle concurrent requests.
R5: The system MUST NOT allow unauthorized access.
R-006: The system MUST be highly available.
R7: WAIVED W1 The system MUST provide an audit trail.
R8: The system MUST be secure.
</contract_rules>

<vocabulary>
Payment: A transfer of funds from a customer to the service.
System: The software and hardware components of the service.
</vocabulary>

<capabilities>
- MAY process payments via Stripe.
- MUST NOT expose internal APIs.
</capabilities>

<coverage>
R1: story__payment_success.md
R2: test_security.py
R3: TODO add logging story
R4: story__concurrent_requests.md
R5: WAIVED W2
R-006: story__high_availability.md
R7: WAIVED W1
R8: test_security_suite.py
</coverage>

<waivers>
W1:
  Rule: R7
  Reason: Audit trail is being implemented in Q3 2024.
  Approved by: Security Team
  Expires: 2024-12-31

W2:
  Rule: R5
  Reason: Temporary waiver for MVP, security hardening planned for next sprint.
  Approved by: Product Owner
  Expires: 2023-01-01 # This waiver is expired for demonstration
</waivers>

<non_responsibilities>
- DOES NOT handle fraud detection directly.
- MAY NOT be used for illegal activities.
</non_responsibilities>
"""
prompt_file_single = output_dir / "prompts" / "my_service.prompt"
create_dummy_file(prompt_file_single, prompt_content_single)

# Run check_prompt
print(f"\nChecking single prompt: {prompt_file_single.name}")
result_single = contract_check.check_prompt(prompt_file_single, strict=False)

print(f"Issues for {result_single.path.name}:")
for issue in result_single.issues:
    print(f"  [{issue.level.upper()}] {issue.code} (Rule: {issue.rule_id}): {issue.message}")
    if issue.suggestion:
        print(f"    Suggestion: {issue.suggestion}")
    if issue.line:
        print(f"    Line: '{issue.line.strip()}'")
print(f"Total warnings: {result_single.warn_count}, Total errors: {result_single.error_count}")
print("--- End check_prompt example ---")


# --- 2. Example for check_directory ---
print("\n--- Running check_directory example ---")

# Create a directory with multiple dummy prompt files
prompts_dir_multi = output_dir / "project" / "prompts"
prompts_dir_multi.mkdir(parents=True, exist_ok=True)

prompt_content_a = """
# Prompt A
<contract_rules>
R1: A MUST do X.
R2: A MUST NOT do Y.
</contract_rules>
<coverage>
R1: story__a_x.md
R2: TODO
</coverage>
"""
create_dummy_file(prompts_dir_multi / "prompt_a.prompt", prompt_content_a)

prompt_content_b = """
# Prompt B
<contract_rules>
R1: B MUST do Z.
R2: B MUST NOT do X.
R3: B MUST do Y.
</contract_rules>
<coverage>
R1: story__b_z.md
R2: WAIVED W1
R3: story__b_y.md
</coverage>
<waivers>
W1:
  Rule: R2
  Reason: Temporary.
  Approved by: Dev
  Expires: 2025-01-01
</waivers>
"""
create_dummy_file(prompts_dir_multi / "sub_dir" / "prompt_b.prompt", prompt_content_b)

print(f"\nChecking directory: {prompts_dir_multi.relative_to(output_dir)}")
results_multi = contract_check.check_directory(prompts_dir_multi, strict=True) # Run in strict mode

for result in results_multi:
    print(f"\nIssues for {result.path.relative_to(output_dir)}:")
    if not result.issues:
        print("  No issues found.")
    for issue in result.issues:
        print(f"  [{issue.level.upper()}] {issue.code} (Rule: {issue.rule_id}): {issue.message}")
        if issue.suggestion:
            print(f"    Suggestion: {issue.suggestion}")
        if issue.line:
            print(f"    Line: '{issue.line.strip()}'")
    print(f"  Total warnings: {result.warn_count}, Total errors: {result.error_count}")
print("--- End check_directory example ---")


# --- 3. Example for check_stories ---
print("\n--- Running check_stories example ---")

# Create a prompts directory for stories to reference
story_prompts_dir = output_dir / "story_project" / "prompts"
story_prompts_dir.mkdir(parents=True, exist_ok=True)

story_prompt_content_1 = """
# Story Prompt 1
<contract_rules>
R1: The user MUST be authenticated.
R2: The system MUST log all access attempts.
R3: The system MAY cache responses.
</contract_rules>
"""
create_dummy_file(story_prompts_dir / "auth_service.prompt", story_prompt_content_1)

story_prompt_content_2 = """
# Story Prompt 2
<contract_rules>
R1: The data MUST be encrypted.
R2: The data SHOULD be backed up daily.
</contract_rules>
"""
create_dummy_file(story_prompts_dir / "data_storage.prompt", story_prompt_content_2)

# Create a stories directory
stories_dir = output_dir / "story_project" / "stories"
stories_dir.mkdir(parents=True, exist_ok=True)

story_content_1 = """
# Story: User Login

<!-- pdd-story-prompts: auth_service.prompt -->

## Covers
- R1: User authentication
- auth_service.prompt#R2: Logging access attempts
- auth_service.prompt#R99: Non-existent rule (will cause a warning)
- data_storage.prompt#R1: Data encryption (cross-prompt reference)
"""
create_dummy_file(stories_dir / "story__user_login.md", story_content_1)

story_content_2 = """
# Story: Data Backup

<!-- pdd-story-prompts: data_storage.prompt -->

## Covers
- R2: Daily backups
- R1: Data encryption (from same prompt)
"""
create_dummy_file(stories_dir / "story__data_backup.md", story_content_2)

print(f"\nChecking stories in: {stories_dir.relative_to(output_dir)}")
print(f"Against prompts in: {story_prompts_dir.relative_to(output_dir)}")
story_results = contract_check.check_stories(stories_dir, story_prompts_dir, strict=False)

for result in story_results:
    print(f"\nIssues for {result.path.relative_to(output_dir)}:")
    if not result.issues:
        print("  No issues found.")
    for issue in result.issues:
        print(f"  [{issue.level.upper()}] {issue.code} (Rule: {issue.rule_id}): {issue.message}")
        if issue.suggestion:
            print(f"    Suggestion: {issue.suggestion}")
        if issue.line:
            print(f"    Line: '{issue.line.strip()}'")
    print(f"  Total warnings: {result.warn_count}, Total errors: {result.error_count}")
print("--- End check_stories example ---")


print(f"\nAll example files created in: {output_dir.resolve()}")
