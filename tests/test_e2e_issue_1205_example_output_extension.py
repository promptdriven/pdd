"""
E2E / integration tests for Issue #1205: `pdd example` silently overrides --output extension.

These tests exercise the full CLI path:
    pdd example PROMPT CODE --output FOO.ext
        -> pdd.commands.generate.example (Click command, --format default="code")
        -> pdd.context_generator_main (extension-preservation guard)
        -> pdd.construct_paths (real, not mocked — language inferred from prompt name)
        -> pdd.construct_paths.BUILTIN_EXT_MAP (lookup table the guard compares against)

Only the LLM-calling boundary (`context_generator`) is mocked. Everything else
between the CLI and the filesystem write runs for real, so the test verifies that
the two-file fix at `0dfaffe` works end-to-end across module boundaries.

The bug it guards against: with `--format` defaulting to `"code"`, the
`format is not None` branch was always taken and `output_path.with_suffix(lang_ext)`
unconditionally rewrote the user's extension. `--output foo.yml` landed at
`foo.yaml`; `--output foo.md` landed at `foo.markdown`.
"""

from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

import pdd
from pdd.cli import cli


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """construct_paths -> _determine_language -> get_language needs PDD_PATH for the CSV lookup."""
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


def _stub_context_generator(content: str):
    """Build a side_effect for `context_generator` returning (code, cost, model)."""
    def _stub(*_args, **_kwargs):
        return content, 0.0, "stub-model"
    return _stub


class TestIssue1205ExampleOutputExtensionE2E:
    """E2E: `pdd example --output foo.<ext>` must land at exactly foo.<ext>."""

    def test_cli_example_yml_output_lands_at_yml_not_yaml(self, tmp_path, monkeypatch):
        """Full CLI: --output ci_example.yml + YAML-language prompt -> file is ci_example.yml."""
        monkeypatch.chdir(tmp_path)
        prompt_file = tmp_path / "ci_YAML.prompt"
        code_file = tmp_path / "ci.yml"
        prompt_file.write_text("Generate a CI workflow example.\n")
        code_file.write_text("name: ci\non: push\njobs: {}\n")
        requested_output = tmp_path / "ci_example.yml"

        runner = CliRunner()
        with patch(
            "pdd.context_generator_main.context_generator",
            side_effect=_stub_context_generator("name: ci\non: push\njobs:\n  test: {}\n"),
        ):
            result = runner.invoke(
                cli,
                [
                    "--local", "--force", "--quiet",
                    "example",
                    str(prompt_file),
                    str(code_file),
                    "--output", str(requested_output),
                ],
            )

        assert result.exit_code == 0, (
            f"pdd example exited {result.exit_code}.\nOutput:\n{result.output}"
        )
        assert requested_output.exists(), (
            f"Bug #1205: requested {requested_output} but it was not written. "
            f"(Likely silently renamed to ci_example.yaml.)\nCLI output:\n{result.output}"
        )
        rewritten = tmp_path / "ci_example.yaml"
        assert not rewritten.exists(), (
            f"Bug #1205: extension silently rewritten from .yml to .yaml; "
            f"unexpected file at {rewritten}"
        )

    def test_cli_example_md_output_lands_at_md_not_markdown(self, tmp_path, monkeypatch):
        """Full CLI: --output impl_example.md + Markdown-language prompt -> file is impl_example.md."""
        monkeypatch.chdir(tmp_path)
        prompt_file = tmp_path / "impl_Markdown.prompt"
        code_file = tmp_path / "impl.md"
        prompt_file.write_text("Generate a markdown example.\n")
        code_file.write_text("# Implementation\n")
        requested_output = tmp_path / "impl_example.md"

        runner = CliRunner()
        with patch(
            "pdd.context_generator_main.context_generator",
            side_effect=_stub_context_generator("# Example\n\nSome markdown body.\n"),
        ):
            result = runner.invoke(
                cli,
                [
                    "--local", "--force", "--quiet",
                    "example",
                    str(prompt_file),
                    str(code_file),
                    "--output", str(requested_output),
                ],
            )

        assert result.exit_code == 0, (
            f"pdd example exited {result.exit_code}.\nOutput:\n{result.output}"
        )
        assert requested_output.exists(), (
            f"Bug #1205: requested {requested_output} but it was not written. "
            f"(Likely silently renamed to impl_example.markdown.)\nCLI output:\n{result.output}"
        )
        rewritten = tmp_path / "impl_example.markdown"
        assert not rewritten.exists(), (
            f"Bug #1205: extension silently rewritten from .md to .markdown; "
            f"unexpected file at {rewritten}"
        )

    def test_cli_example_py_output_regression(self, tmp_path, monkeypatch):
        """Regression: Python --output foo.py keeps landing at foo.py (was already correct, must stay correct)."""
        monkeypatch.chdir(tmp_path)
        prompt_file = tmp_path / "auth_python.prompt"
        code_file = tmp_path / "auth.py"
        prompt_file.write_text("Generate an auth example.\n")
        code_file.write_text("def auth():\n    return True\n")
        requested_output = tmp_path / "auth_example.py"

        runner = CliRunner()
        with patch(
            "pdd.context_generator_main.context_generator",
            side_effect=_stub_context_generator("def auth_example():\n    return True\n"),
        ):
            result = runner.invoke(
                cli,
                [
                    "--local", "--force", "--quiet",
                    "example",
                    str(prompt_file),
                    str(code_file),
                    "--output", str(requested_output),
                ],
            )

        assert result.exit_code == 0, (
            f"pdd example exited {result.exit_code}.\nOutput:\n{result.output}"
        )
        assert requested_output.exists()
        assert requested_output.read_text().startswith("def auth_example")

    def test_cli_example_yaml_output_alias_lands_at_yaml(self, tmp_path, monkeypatch):
        """The other YAML alias: --output foo.yaml + YAML prompt must also land at foo.yaml unchanged."""
        monkeypatch.chdir(tmp_path)
        prompt_file = tmp_path / "ci_YAML.prompt"
        code_file = tmp_path / "ci.yaml"
        prompt_file.write_text("Generate a CI workflow example.\n")
        code_file.write_text("name: ci\n")
        requested_output = tmp_path / "ci_example.yaml"

        runner = CliRunner()
        with patch(
            "pdd.context_generator_main.context_generator",
            side_effect=_stub_context_generator("name: ci\njobs: {}\n"),
        ):
            result = runner.invoke(
                cli,
                [
                    "--local", "--force", "--quiet",
                    "example",
                    str(prompt_file),
                    str(code_file),
                    "--output", str(requested_output),
                ],
            )

        assert result.exit_code == 0, (
            f"pdd example exited {result.exit_code}.\nOutput:\n{result.output}"
        )
        assert requested_output.exists()
        # And the .yml twin must not have been created
        assert not (tmp_path / "ci_example.yml").exists()


class TestIssue1205BuiltinExtMapIntegration:
    """Cross-module: confirm the BUILTIN_EXT_MAP change in construct_paths flows
    into context_generator_main's lookup correctly (these two modules are the
    fix surface; this verifies they agree on what `lang_key='markdown'` maps to)."""

    def test_builtin_ext_map_markdown_drives_context_generator_main_default_path(
        self, tmp_path, monkeypatch
    ):
        """When no --output is supplied for a Markdown prompt, the auto-generated path
        must use .md (from the new BUILTIN_EXT_MAP entry), not the .markdown fallback."""
        monkeypatch.chdir(tmp_path)
        # Sanity-check the cross-module contract that context_generator_main relies on.
        from pdd.construct_paths import BUILTIN_EXT_MAP
        assert BUILTIN_EXT_MAP.get("markdown") == ".md", (
            "BUILTIN_EXT_MAP must define 'markdown' -> '.md' so context_generator_main's "
            "BUILTIN_EXT_MAP.get(lang_key, f'.{lang_key}') lookup does not fall through "
            "to the synthesized '.markdown' value."
        )
        assert BUILTIN_EXT_MAP.get("yaml") == ".yaml"
        assert BUILTIN_EXT_MAP.get("yml") == ".yml"
