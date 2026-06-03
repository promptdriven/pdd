import sys
import types
import json
import os
import pytest
from unittest.mock import MagicMock, patch
import importlib
from click.testing import CliRunner

# We need to mock the dependencies BEFORE importing pdd.cli to ensure isolation
# and to capture the side effects of the module-level code.

@pytest.fixture
def mock_pdd_dependencies():
    """
    Sets up mocks for all modules that pdd.cli imports.
    This prevents actual imports and allows us to verify interactions.
    """
    # Create a dictionary of modules to mock
    modules_to_mock = [
        'pdd.core',
        'pdd.core.cli',
        'pdd.commands',
        'pdd.commands.templates',
        'pdd.auto_update',
        'pdd.code_generator_main',
        'pdd.context_generator_main',
        'pdd.cmd_test_main',
        'pdd.fix_main',
        'pdd.split_main',
        'pdd.change_main',
        'pdd.update_main',
        'pdd.sync_main',
        'pdd.auto_deps_main',
        'pdd.detect_change_main',
        'pdd.conflicts_main',
        'pdd.bug_main',
        'pdd.crash_main',
        'pdd.trace_main',
        'pdd.agentic_test',
        'pdd.preprocess_main',
        'pdd.construct_paths',
        'pdd.fix_verification_main',
        'pdd.core.errors',
        'pdd.install_completion',
        'pdd.core.utils',
    ]

    mock_modules = {}
    original_modules = {}

    # Setup mocks
    for mod_name in modules_to_mock:
        if mod_name in sys.modules:
            original_modules[mod_name] = sys.modules[mod_name]
        
        mock_mod = MagicMock()
        sys.modules[mod_name] = mock_mod
        mock_modules[mod_name] = mock_mod

    # Specific setup for attributes accessed in pdd.cli
    # pdd.core.cli.cli
    mock_modules['pdd.core.cli'].cli = MagicMock(name='cli_group')
    mock_modules['pdd.core.cli'].process_commands = MagicMock(name='process_commands')
    
    # pdd.commands.register_commands
    mock_modules['pdd.commands'].register_commands = MagicMock(name='register_commands')

    # Setup dummy attributes for re-exports to verify they are passed through
    mock_modules['pdd.commands.templates'].templates_group = "mock_templates_group"
    mock_modules['pdd.auto_update'].auto_update = "mock_auto_update"
    mock_modules['pdd.code_generator_main'].code_generator_main = "mock_code_generator_main"
    # ... (we can check existence for others, explicit values help debugging)

    yield mock_modules

    # Teardown: Restore original modules
    for mod_name in modules_to_mock:
        if mod_name in original_modules:
            sys.modules[mod_name] = original_modules[mod_name]
        else:
            del sys.modules[mod_name]
            
    # Also remove pdd.cli from sys.modules so it gets re-imported cleanly next time
    if 'pdd.cli' in sys.modules:
        del sys.modules['pdd.cli']

    # Remove the cached 'cli' attribute on the pdd package so that
    # subsequent `from pdd import cli` triggers a fresh re-import
    # instead of returning the stale module with mocked dependencies.
    pdd_pkg = sys.modules.get('pdd')
    if pdd_pkg is not None and hasattr(pdd_pkg, 'cli'):
        delattr(pdd_pkg, 'cli')


def test_cli_registers_commands_on_import(mock_pdd_dependencies):
    """
    Test that importing pdd.cli calls register_commands(cli).
    """
    # Arrange
    mock_cli_group = mock_pdd_dependencies['pdd.core.cli'].cli
    mock_register = mock_pdd_dependencies['pdd.commands'].register_commands

    # Act
    # Ensure pdd.cli is not in sys.modules so import triggers execution
    if 'pdd.cli' in sys.modules:
        del sys.modules['pdd.cli']
    import pdd.cli

    # Assert
    mock_register.assert_called_once_with(mock_cli_group)


def test_cli_re_exports_symbols(mock_pdd_dependencies):
    """
    Test that pdd.cli re-exports the expected symbols from submodules.
    """
    # Arrange
    # Define the list of expected exports based on the code under test
    expected_exports = [
        'templates_group',
        'auto_update',
        'code_generator_main',
        'context_generator_main',
        'cmd_test_main',
        'fix_main',
        'split_main',
        'change_main',
        'update_main',
        'sync_main',
        'auto_deps_main',
        'detect_change_main',
        'conflicts_main',
        'bug_main',
        'crash_main',
        'trace_main',
        'agentic_test_main',
        'preprocess_main',
        'construct_paths',
        'fix_verification_main',
        'console',
        'install_completion',
        '_should_show_onboarding_reminder',
        'process_commands'
    ]

    # Act
    if 'pdd.cli' in sys.modules:
        del sys.modules['pdd.cli']
    import pdd.cli

    # Assert
    for symbol in expected_exports:
        assert hasattr(pdd.cli, symbol), f"pdd.cli is missing re-export: {symbol}"


def test_cli_main_execution_logic(mock_pdd_dependencies):
    """
    Test the logic that would run under if __name__ == \"__main__\":
    Since we cannot easily invoke __main__ directly without subprocesses,
    we verify the components that would be called are present and correct.
    """
    # Arrange
    mock_cli_group = mock_pdd_dependencies['pdd.core.cli'].cli
    
    # Act
    if 'pdd.cli' in sys.modules:
        del sys.modules['pdd.cli']
    import pdd.cli

    # Assert
    # We verify that the 'cli' object imported into pdd.cli is indeed the one we mocked.
    # This confirms that if `cli()` were called in main, it would be our mock.
    assert pdd.cli.cli is mock_cli_group
    
    # If we were to simulate main:
    with patch.object(pdd.cli, 'cli') as mocked_main_cli:
        # We can't easily trigger the if block without executing the file as a script.
        # But we can verify the object is callable.
        assert callable(pdd.cli.cli)


def _estimate_payload(command: str = "generate"):
    return {
        "estimate": True,
        "command": command,
        "model": "gpt-5-nano",
        "pricing_model": "gpt-5-nano",
        "input_tokens": 100,
        "predicted_output_tokens": 75,
        "output_ratio": 0.75,
        "input_rate_per_million": 2.0,
        "output_rate_per_million": 4.0,
        "input_cost": 0.0002,
        "output_cost": 0.0003,
        "estimated_cost": 0.0005,
        "total_cost": 0.0005,
        "unknown_cost": False,
        "cost_known": True,
        "currency": "USD",
        "context_limit": 1000,
        "context_usage_percent": 10.0,
        "call_type": "completion",
        "provider_call_made": False,
        "attempted_models": ["gpt-5-nano"],
    }


def test_cli_estimate_generate_prints_table_and_writes_no_files(tmp_path, monkeypatch):
    import pdd.cli  # noqa: F401 - registers commands on the core CLI
    from pdd.core.cli import cli as real_cli
    from pdd.llm_invoke import EstimateOnlyResult

    prompt = tmp_path / "demo_python.prompt"
    output = tmp_path / "demo.py"
    cost_csv = tmp_path / "cost.csv"
    prompt.write_text("% Generate demo code\n", encoding="utf-8")

    def fake_code_generator_main(**kwargs):
        ctx = kwargs["ctx"]
        assert ctx.obj["estimate"] is True
        assert ctx.obj["output_cost"] is None
        assert ctx.obj["local"] is True
        assert ctx.obj["force"] is True
        assert "PDD_OUTPUT_COST_PATH" not in os.environ
        import pdd.code_generator_main as code_generator_module

        assert code_generator_module.incremental_code_generator_func() == (
            None,
            False,
            0.0,
            "estimate",
        )
        raise EstimateOnlyResult(_estimate_payload())

    monkeypatch.setenv("PDD_OUTPUT_COST_PATH", str(cost_csv))
    with patch("pdd.commands.generate.code_generator_main", fake_code_generator_main):
        result = CliRunner().invoke(
            real_cli,
            [
                "--dry-run-cost",
                "--output-cost", str(cost_csv),
                "--no-core-dump",
                "generate",
                "--output", str(output),
                str(prompt),
            ],
        )

    assert result.exit_code == 0, result.output
    assert "LLM Cost Estimate" in result.output
    assert "gpt-5-nano" in result.output
    assert "Input Tokens" in result.output
    assert "Predicted Output Tokens" in result.output
    assert "Total estimated cost: $0.000500" in result.output
    assert "Provider call made: false" in result.output
    assert not output.exists()
    assert not cost_csv.exists()


def test_cli_estimate_json_generate_outputs_machine_payload(tmp_path):
    import pdd.cli  # noqa: F401 - registers commands on the core CLI
    from pdd.core.cli import cli as real_cli
    from pdd.llm_invoke import EstimateOnlyResult

    prompt = tmp_path / "demo_python.prompt"
    prompt.write_text("% Generate demo code\n", encoding="utf-8")

    with patch(
        "pdd.commands.generate.code_generator_main",
        side_effect=EstimateOnlyResult(_estimate_payload()),
    ):
        result = CliRunner().invoke(
            real_cli,
            ["--estimate-json", "--no-core-dump", "generate", str(prompt)],
        )

    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["estimate"] is True
    assert payload["estimated_cost"] == 0.0005
    assert payload["unknown_cost"] is False
    assert payload["records"][0]["provider_call_made"] is False
    assert "Command Execution Summary" not in result.output
    assert "Generate demo code" not in result.output


def test_cli_estimate_test_story_generation_rejected_without_writes(tmp_path):
    import pdd.cli  # noqa: F401 - registers commands on the core CLI
    from pdd.core.cli import cli as real_cli

    prompt = tmp_path / "demo_python.prompt"
    story_output = tmp_path / "story__demo.md"
    prompt.write_text("% Generate demo code\n", encoding="utf-8")

    with patch("pdd.commands.generate.generate_user_story") as mock_generate_story:
        result = CliRunner().invoke(
            real_cli,
            [
                "--estimate",
                "--no-core-dump",
                "test",
                "--output", str(story_output),
                str(prompt),
            ],
        )

    assert result.exit_code == 2, result.output
    assert "Estimate mode is not supported for story generation" in result.output
    assert not story_output.exists()
    mock_generate_story.assert_not_called()


def test_cli_estimate_test_story_metadata_rejected_without_writes(tmp_path):
    import pdd.cli  # noqa: F401 - registers commands on the core CLI
    from pdd.core.cli import cli as real_cli

    story = tmp_path / "story__demo.md"
    original = "# Story\n\nNo metadata yet.\n"
    story.write_text(original, encoding="utf-8")

    with patch("pdd.commands.generate.cache_story_prompt_links") as mock_link_story:
        result = CliRunner().invoke(
            real_cli,
            ["--estimate", "--no-core-dump", "test", str(story)],
        )

    assert result.exit_code == 2, result.output
    assert "Estimate mode is not supported for story metadata linking" in result.output
    assert story.read_text(encoding="utf-8") == original
    mock_link_story.assert_not_called()


def test_load_prompt_template_suppresses_chatter_in_estimate_json(tmp_path, monkeypatch):
    import click
    from pdd.load_prompt_template import load_prompt_template

    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    (prompts_dir / "demo.prompt").write_text("template body", encoding="utf-8")
    monkeypatch.setenv("PDD_PATH", str(tmp_path))

    @click.command()
    @click.pass_context
    def command(ctx):
        ctx.obj = {"estimate": True, "estimate_json": True, "quiet": True}
        assert load_prompt_template("demo") == "template body"
        click.echo("done")

    result = CliRunner().invoke(command)

    assert result.exit_code == 0, result.output
    assert result.output == "done\n"


def test_cli_estimate_json_conflicts_rejected_before_template_loading(tmp_path):
    import pdd.cli  # noqa: F401 - registers commands on the core CLI
    from pdd.core.cli import cli as real_cli

    prompt1 = tmp_path / "a_python.prompt"
    prompt2 = tmp_path / "b_python.prompt"
    output = tmp_path / "conflicts.csv"
    prompt1.write_text("% prompt a\n", encoding="utf-8")
    prompt2.write_text("% prompt b\n", encoding="utf-8")

    with patch("pdd.commands.analysis.conflicts_main") as mock_conflicts_main:
        result = CliRunner().invoke(
            real_cli,
            [
                "--estimate-json",
                "--no-core-dump",
                "conflicts",
                "--output", str(output),
                str(prompt1),
                str(prompt2),
            ],
        )

    assert result.exit_code == 2, result.output
    assert "Estimate mode is not supported for conflicts" in result.output
    assert "Successfully loaded prompt" not in result.output
    assert not output.exists()
    mock_conflicts_main.assert_not_called()


def test_cli_estimate_crash_rejected_without_writes(tmp_path):
    import pdd.cli  # noqa: F401 - registers commands on the core CLI
    from pdd.core.cli import cli as real_cli

    prompt = tmp_path / "demo_python.prompt"
    code = tmp_path / "demo.py"
    program = tmp_path / "run_demo.py"
    errors = tmp_path / "errors.log"
    output = tmp_path / "fixed_demo.py"
    output_program = tmp_path / "fixed_run_demo.py"
    prompt.write_text("% prompt\n", encoding="utf-8")
    code.write_text("def demo():\n    return 1\n", encoding="utf-8")
    program.write_text("from demo import demo\nprint(demo())\n", encoding="utf-8")
    errors.write_text("Traceback\n", encoding="utf-8")

    with patch("pdd.commands.analysis.crash_main") as mock_crash_main:
        result = CliRunner().invoke(
            real_cli,
            [
                "--estimate",
                "--no-core-dump",
                "crash",
                "--output", str(output),
                "--output-program", str(output_program),
                str(prompt),
                str(code),
                str(program),
                str(errors),
            ],
        )

    assert result.exit_code == 2, result.output
    assert "Estimate mode is not supported for crash" in result.output
    assert not output.exists()
    assert not output_program.exists()
    mock_crash_main.assert_not_called()


def test_cli_estimate_fix_rejected_before_manual_helper(tmp_path):
    import pdd.cli  # noqa: F401 - registers commands on the core CLI
    from pdd.core.cli import cli as real_cli

    prompt = tmp_path / "demo_python.prompt"
    code = tmp_path / "demo.py"
    tests = tmp_path / "test_demo.py"
    errors = tmp_path / "errors.log"
    output_code = tmp_path / "fixed_demo.py"
    output_test = tmp_path / "fixed_test_demo.py"
    prompt.write_text("% prompt\n", encoding="utf-8")
    code.write_text("def demo():\n    return 1\n", encoding="utf-8")
    tests.write_text("def test_demo():\n    assert True\n", encoding="utf-8")
    errors.write_text("failure\n", encoding="utf-8")

    result = CliRunner().invoke(
        real_cli,
        [
            "--estimate",
            "--no-core-dump",
            "fix",
            "--output-code", str(output_code),
            "--output-test", str(output_test),
            str(prompt),
            str(code),
            str(tests),
            str(errors),
        ],
    )

    assert result.exit_code == 2, result.output
    assert "Estimate mode is not supported for manual fix" in result.output
    assert not output_code.exists()
    assert not output_test.exists()
