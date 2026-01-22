import re

from click.testing import CliRunner

# Helper to clean non-deterministic updater chatter from CLI output.
def _clean_pdd_output(output: str) -> str:
    """Strip non-deterministic updater chatter from CLI output.

    Some environments print an update check banner / prompt before command output.
    Tests should validate `pdd which` behavior, not the updater.
    """
    drop_prefixes = (
        "Checking for updates...",
        "New version of pdd-cli available:",
        "Would you like to upgrade?",
        "Error checking for updates:",
    )
    kept: list[str] = []
    for raw in (output or "").splitlines():
        line = raw.strip()
        if not line:
            kept.append(raw)
            continue
        if any(line.startswith(p) for p in drop_prefixes):
            continue
        kept.append(raw)
    return "\n".join(kept)


def _parse_kv_output(output: str) -> dict[str, str]:
    """Parse `pdd which` output in a tolerant way.

    Expected format is key/value pairs, one per line, using either `key=value` or `key: value`.
    We intentionally keep this parser permissive so the tests validate behavior without
    over-constraining formatting.
    """
    kv: dict[str, str] = {}
    for raw in _clean_pdd_output(output).splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if "=" in line:
            k, v = line.split("=", 1)
        elif ":" in line:
            k, v = line.split(":", 1)
        else:
            continue
        k = k.strip().lower()
        v = v.strip()
        if k:
            kv[k] = v
    return kv


def _run_pdd_which(args: list[str], env: dict[str, str] | None = None, cwd: str | None = None):
    """Invoke `pdd which ...` via the Click CLI."""
    # Import inside helper so test collection doesn't fail if CLI wiring changes.
    from pdd.cli import cli

    runner = CliRunner(mix_stderr=False)
    return runner.invoke(cli, ["which", *args], env=env, catch_exceptions=False, prog_name="pdd")


def test_which_runs_and_reports_context_none_when_no_config(tmp_path, monkeypatch):
    """With no .pddrc and no env overrides, `pdd which` should report context as none."""
    # Ensure no env hints are present.
    monkeypatch.delenv("PDD_CONTEXT", raising=False)
    monkeypatch.delenv("PDD_PROMPTS_DIR", raising=False)
    monkeypatch.delenv("PDD_PROMPT_PATH", raising=False)

    # Run in an empty directory.
    monkeypatch.chdir(tmp_path)

    result = _run_pdd_which([])
    assert result.exit_code == 0, result.output

    out = _clean_pdd_output(result.output or "")
    kv = _parse_kv_output(out)

    # Be tolerant: accept either explicit key or a human-readable line containing both words.
    if "context" in kv:
        assert kv["context"].strip().lower() in {"none", "null", ""}
    else:
        assert re.search(r"(?i)context\s*[:=]\s*none", out) is not None


def test_which_respects_explicit_context_flag(tmp_path, monkeypatch):
    """If a context is provided explicitly, `pdd which` should print that context name."""
    # Minimal .pddrc so context name is meaningful.
    # (We keep it minimal so it won't drift with unrelated config evolution.)
    (tmp_path / ".pddrc").write_text(
        """
contexts:
  default:
    defaults:
      prompts_dir: prompts
""".lstrip()
    )

    monkeypatch.chdir(tmp_path)

    # Many PDD commands accept `--context`; this test asserts `which` does too.
    result = _run_pdd_which(["--context", "default"])
    assert result.exit_code == 0, result.output

    out = _clean_pdd_output(result.output or "")
    kv = _parse_kv_output(out)
    if "context" in kv:
        assert kv["context"].strip().lower() == "default"
    else:
        assert re.search(r"(?i)context\s*[:=]\s*default", out) is not None


def _extract_search_paths(output: str, section_key: str) -> list[str]:
    """Extract the list items printed under `<section_key>:`.

    This is intentionally tolerant of formatting; it looks for a line that starts with
    the section key (case-insensitive) and then captures subsequent list items that
    begin with `- ` until the next non-indented key/section.
    """
    lines = _clean_pdd_output(output).splitlines()
    target = section_key.strip().lower()
    start = None
    for i, raw in enumerate(lines):
        line = raw.strip().lower()
        if line == target:
            start = i + 1
            break
        # Allow either `key:` or `key :` (whitespace before colon)
        if line.startswith(target) and line[len(target):].lstrip().startswith(":"):
            start = i + 1
            break
    if start is None:
        return []

    paths: list[str] = []
    for raw in lines[start:]:
        # Stop when we hit a new top-level label / section
        if raw and not raw.startswith(" ") and not raw.startswith("\t") and not raw.lstrip().startswith("-"):
            break
        stripped = raw.strip()
        if stripped.startswith("-"):
            item = stripped[1:].strip()
            if item:
                paths.append(item)
    return paths


def test_which_shows_prompt_path_env_precedence(tmp_path, monkeypatch):
    """PDD_PROMPT_PATH should win over PDD_PROMPTS_DIR and be visible in output."""
    (tmp_path / ".pddrc").write_text(
        """
contexts:
  default:
    defaults:
      prompts_dir: prompts
""".lstrip()
    )

    monkeypatch.chdir(tmp_path)

    monkeypatch.setenv("PDD_PROMPT_PATH", "/tmp/custom_prompts")
    monkeypatch.setenv("PDD_PROMPTS_DIR", "/tmp/other_prompts")

    result = _run_pdd_which(["--context", "default"])
    assert result.exit_code == 0, result.output

    out = _clean_pdd_output(result.output or "")
    kv = _parse_kv_output(out)

    # Prefer asserting on the concrete search paths list, which reflects actual lookup behavior.
    prompt_paths = _extract_search_paths(out, "prompts.search_paths")
    assert prompt_paths, f"Expected prompts.search_paths to be printed. Output was:\n{out}"

    # Env PDD_PROMPT_PATH should win over PDD_PROMPTS_DIR; it should appear first.
    assert prompt_paths[0].endswith("/custom_prompts")
    assert not prompt_paths[0].endswith("/other_prompts")


# Supplementary tests for explicit env/config search path handling
def test_which_shows_prompts_dir_env_when_prompt_path_unset(tmp_path, monkeypatch):
    """When only PDD_PROMPTS_DIR is set, it should appear at the front of prompts.search_paths."""
    (tmp_path / ".pddrc").write_text(
        """
contexts:
  default:
    defaults:
      prompts_dir: prompts
""".lstrip()
    )

    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_PROMPT_PATH", raising=False)
    monkeypatch.setenv("PDD_PROMPTS_DIR", "/tmp/other_prompts")

    result = _run_pdd_which(["--context", "default"])
    assert result.exit_code == 0, result.output

    out = _clean_pdd_output(result.output or "")
    prompt_paths = _extract_search_paths(out, "prompts.search_paths")
    assert prompt_paths, f"Expected prompts.search_paths to be printed. Output was:\n{out}"

    # PDD_PROMPTS_DIR should be first when PDD_PROMPT_PATH is unset.
    assert prompt_paths[0].endswith("/other_prompts")


def test_which_includes_config_prompts_dir_in_search_paths(tmp_path, monkeypatch):
    """The configured prompts_dir should be present among prompts.search_paths."""
    (tmp_path / ".pddrc").write_text(
        """
contexts:
  default:
    defaults:
      prompts_dir: prompts
""".lstrip()
    )

    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_PROMPT_PATH", raising=False)
    monkeypatch.delenv("PDD_PROMPTS_DIR", raising=False)

    result = _run_pdd_which(["--context", "default"])
    assert result.exit_code == 0, result.output

    out = _clean_pdd_output(result.output or "")
    prompt_paths = _extract_search_paths(out, "prompts.search_paths")
    assert prompt_paths, f"Expected prompts.search_paths to be printed. Output was:\n{out}"

    # The repo-relative prompts_dir should resolve under the config base.
    assert any(p.endswith("/prompts") for p in prompt_paths)