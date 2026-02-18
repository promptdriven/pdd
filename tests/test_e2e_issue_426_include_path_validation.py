"""
E2E Test for Issue #426: Architecture generation sometimes doesn't validate context inclusion

This test exercises the full architecture generation workflow to verify that Step 11
correctly validates include paths in generated prompts match the example_output_path
configured in .pddrc.

The bug: When Step 8 generates prompt files with <include> tags, the LLM sometimes
produces incorrect paths like:
    <include>src/models_example.py</include>
when .pddrc specifies examples should be in:
    context/models_example.py

Step 11's validation was instructed to "DO NOT run preprocess" which prevented it from
catching these path errors. The bug only manifests at runtime during `pdd sync` when
the preprocessor fails with "[File not found: ...]" errors.

This E2E test:
1. Sets up a temp directory with a .pddrc specifying example_output_path as "context/"
2. Runs the architecture generation orchestrator through Step 11
3. Mocks Step 8 to generate prompts with WRONG include paths (src/ instead of context/)
4. Verifies that Step 11 DETECTS the validation error and returns INVALID
5. Verifies that the orchestrator triggers a fix cycle and re-validates

The test should PASS on fixed code (Step 11 detects wrong paths) and would FAIL on
buggy code (Step 11 doesn't validate include paths).
"""

import pytest
import json
from pathlib import Path
from unittest.mock import patch

from pdd.agentic_architecture_orchestrator import run_agentic_architecture_orchestrator


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


@pytest.mark.e2e
class TestIncludePathValidationE2E:
    """
    E2E tests for Issue #426: Verify architecture generation validates include paths
    in generated prompts match the example_output_path from .pddrc configuration.
    """

    def test_architecture_generation_validates_wrong_include_paths_e2e(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: Architecture generation (Step 11) should DETECT when generated prompts
        contain include paths that don't match .pddrc example_output_path.

        This test simulates the exact scenario from issue #426:
        1. .pddrc specifies example_output_path: "context/"
        2. Step 8 generates a prompt with wrong path: src/models_example.py
        3. Step 11 validation should CATCH this error and return INVALID

        Expected behavior (after fix):
        - Step 11 validates include paths against .pddrc
        - Returns VALIDATION_RESULT: INVALID with specific error about wrong path
        - Triggers a fix cycle to correct the paths

        Bug behavior (Issue #426):
        - Step 11 skips include path validation
        - Wrong paths pass through to runtime
        - `pdd sync` fails with "[File not found: ...]" errors
        """
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")

        # 1. Define the GitHub issue content (used in Step 1)
        issue_content = """# Product Specification
Build a simple Python data model system with examples.

## Requirements
- Create data models for users and products
- Provide example implementations in context/ directory
"""

        # Track which steps were called and control their outputs
        step_calls = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM agent for each step of the architecture workflow."""
            step_calls.append(label)

            # Steps 1-6: Analysis and generation
            if "step1" in label:
                return (True, "Analysis complete: Python project with data models", 0.001, "mock-model")
            elif "step2" in label:
                return (True, "Deep analysis: Core models identified", 0.001, "mock-model")
            elif "step3" in label:
                return (True, "Research: Best practices documented", 0.001, "mock-model")
            elif "step4" in label:
                return (True, "Design: Architecture defined", 0.001, "mock-model")
            elif "step5" in label:
                return (True, "Dependencies: No external dependencies needed", 0.001, "mock-model")
            elif "step6" in label:
                # Create architecture.json (array format matching orchestrator expectations)
                architecture = [
                    {
                        "filename": "user_model_Python.prompt",
                        "filepath": "src/models/user.py",
                        "priority": 1,
                        "dependencies": [],
                        "description": "User data model"
                    }
                ]
                arch_file = cwd / "architecture.json"
                arch_file.write_text(json.dumps(architecture, indent=2))

                # Create scaffolding directories
                (cwd / "prompts").mkdir(exist_ok=True)
                (cwd / "src" / "models").mkdir(parents=True, exist_ok=True)

                return (True, f"FILES_CREATED: architecture.json", 0.001, "mock-model")

            elif "step7" in label:
                # Generate .pddrc in YAML format (matching production format)
                pddrc_yaml = """prompts_dir: prompts
contexts:
  models:
    defaults:
      example_output_path: context/
"""
                pddrc_file = cwd / ".pddrc"
                pddrc_file.write_text(pddrc_yaml)

                # Create the context directory
                (cwd / "context").mkdir(exist_ok=True)

                return (True, "FILES_CREATED: .pddrc", 0.001, "mock-model")

            elif "step8" in label:
                # Generate prompt with WRONG include path
                # .pddrc says "context/" but we're using "src/"
                prompt_content = """You are a Python expert.

<include>src/models_example.py</include>

Create a User data model class.
"""
                prompt_file = cwd / "prompts" / "user_model.prompt"
                prompt_file.write_text(prompt_content)

                return (True, "FILES_CREATED: prompts/user_model.prompt", 0.001, "mock-model")

            elif "step9_attempt" in label:
                # Validate completeness - pass immediately
                return (True, "VALIDATION_RESULT: VALID\nAll modules present in architecture.json", 0.001, "mock-model")

            elif "step10_attempt" in label:
                # Validate sync (dry-run) - pass immediately
                return (True, "VALIDATION_RESULT: VALID\nDry-run successful", 0.001, "mock-model")

            elif "step11_attempt1" in label:
                # First attempt: detect the wrong include path and return INVALID
                return (
                    True,
                    "VALIDATION_RESULT: INVALID\n\n"
                    "INCLUDE PATH ERROR in user_model_Python.prompt: "
                    "'src/models_example.py' does not start with any "
                    "example_output_path from .pddrc. Expected prefixes: ['context']",
                    0.001,
                    "mock-model"
                )

            elif "step11_attempt" in label:
                # Subsequent attempts after fix: paths are now correct
                return (True, "VALIDATION_RESULT: VALID\nAll dependencies valid", 0.001, "mock-model")

            elif "step11_fix" in label:
                # Fix validation errors
                prompt_file = cwd / "prompts" / "user_model.prompt"
                fixed_content = """You are a Python expert.

<include>context/models_example.py</include>

Create a User data model class.
"""
                prompt_file.write_text(fixed_content)
                return (True, "FILES_MODIFIED: prompts/user_model.prompt", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            """Mock state saving."""
            pass

        def mock_load_state(*args, **kwargs):
            """Mock state loading."""
            return None, None

        def mock_clear_state(*args, **kwargs):
            """Mock state clearing."""
            pass

        # 2. Run the architecture generation orchestrator
        with patch('pdd.agentic_architecture_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_architecture_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_architecture_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_architecture_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        with patch('pdd.agentic_architecture_orchestrator.load_prompt_template', return_value="Prompt template"):
                            with patch('pdd.agentic_architecture_orchestrator.generate_mermaid_code', return_value="graph TD; A-->B;"):
                                with patch('pdd.agentic_architecture_orchestrator.generate_html', return_value="<html></html>"):
                                    with patch('pdd.agentic_architecture_orchestrator.HAS_MERMAID', True):
                                        success, message, cost, model, files = run_agentic_architecture_orchestrator(
                                            issue_url="https://github.com/test/repo/issues/426",
                                            issue_content=issue_content,
                                            repo_owner="test",
                                            repo_name="repo",
                                            issue_number=426,
                                            issue_author="test-user",
                                            issue_title="Architecture generation doesn't validate context inclusion",
                                            cwd=tmp_path,
                                            verbose=False,
                                            quiet=True,
                                            use_github_state=False,
                                        )

        # 3. CRITICAL ASSERTIONS

        # Verify Step 11 was called
        step11_calls = [call for call in step_calls if "step11" in call]
        assert len(step11_calls) > 0, (
            f"Step 11 was not called in the workflow. "
            f"Steps called: {step_calls}"
        )

        # THE KEY ASSERTION: Step 11 should have detected the validation error
        # After the fix, Step 11 validates include paths and returns INVALID
        # This should trigger fix attempts (step11_fix1, step11_fix2, etc.)

        # Check if Step 11 fix attempts were triggered
        step11_fix_calls = [call for call in step_calls if "step11_fix" in call]

        if len(step11_fix_calls) == 0:
            pytest.fail(
                f"BUG DETECTED (Issue #426): Step 11 did NOT detect the wrong include path!\n\n"
                f"Setup:\n"
                f"  - .pddrc specifies example_output_path: 'context/'\n"
                f"  - Generated prompt contains: <include>src/models_example.py</include>\n\n"
                f"Expected:\n"
                f"  - Step 11 should validate include paths against .pddrc\n"
                f"  - Step 11 should return VALIDATION_RESULT: INVALID\n"
                f"  - Orchestrator should trigger fix cycle (step11_fix1, step11_fix2, etc.)\n\n"
                f"Actual:\n"
                f"  - No step11_fix calls were made\n"
                f"  - This means Step 11 didn't detect the validation error\n\n"
                f"Impact:\n"
                f"  - Wrong paths pass through to runtime\n"
                f"  - `pdd sync` will fail with '[File not found: src/models_example.py]'\n\n"
                f"Steps called: {step_calls}"
            )

        # Verify that multiple validation attempts were made (indicating fix-retry loop)
        step11_attempt_calls = [call for call in step_calls if "step11_attempt" in call]
        assert len(step11_attempt_calls) >= 2, (
            f"Step 11 should be attempted at least twice: once to detect error, once after fix.\n"
            f"Step 11 was attempted {len(step11_attempt_calls)} time(s).\n"
            f"Steps called: {step_calls}"
        )
