"""
E2E Test for Issue #551: `pdd example` ignores explicit --output filename.

This test exercises the full CLI path:
`pdd.cli:cli -> commands.generate.example -> context_generator_main`.

Only the LLM boundary is mocked (`context_generator`) so the real path
resolution and output-file writing logic runs unchanged.
"""

from unittest.mock import patch

from click.testing import CliRunner


def test_e2e_example_preserves_explicit_output_filename_for_typescriptreact(tmp_path):
    """
    Regression test for issue #551.

    User-facing expectation:
    - When `--output` provides a complete filename, PDD should write exactly
      that filename.

    Buggy behavior:
    - For `--format code`, context_generator_main rewrites the suffix based on
      detected language and ignores the explicit user-provided filename.
    """
    project = tmp_path / "project"
    prompts_dir = project / "prompts"
    src_dir = project / "src"
    prompts_dir.mkdir(parents=True)
    src_dir.mkdir(parents=True)

    prompt_file = prompts_dir / "app_page_TypeScriptReact.prompt"
    code_file = src_dir / "app_page.tsx"
    prompt_file.write_text("% Generate an example for this TSX module.\n", encoding="utf-8")
    code_file.write_text("export function AppPage() { return <div>Hello</div>; }\n", encoding="utf-8")

    # Intentionally use a complete explicit filename that does NOT end in .tsx.
    # --output should be respected exactly.
    explicit_output = project / "examples" / "app" / "app_page_example.tsx.bak"
    rewritten_output = explicit_output.with_suffix(".tsx")

    from pdd.cli import cli

    runner = CliRunner()
    with patch("pdd.context_generator_main.context_generator", return_value=("// generated example\n", 0.0, "mock-model")):
        result = runner.invoke(
            cli,
            [
                "--quiet",
                "--local",
                "example",
                str(prompt_file),
                str(code_file),
                "--output",
                str(explicit_output),
            ],
            catch_exceptions=False,
        )

    assert result.exit_code == 0, f"CLI failed unexpectedly: {result.output}"
    assert explicit_output.exists() and not rewritten_output.exists(), (
        "Issue #551: explicit --output filename was not preserved.\n"
        f"Expected exact output path to exist: {explicit_output} -> {explicit_output.exists()}\n"
        f"Expected rewritten language path to NOT exist: {rewritten_output} -> {rewritten_output.exists()}\n"
        f"CLI output:\n{result.output}"
    )
