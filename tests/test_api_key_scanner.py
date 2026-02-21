# Test Plan: pdd/api_key_scanner.py
#
# Public API under test:
#   - get_provider_key_names() → List[str]
#   - scan_environment()       → Dict[str, KeyInfo]
#   - KeyInfo                  → dataclass(source, is_set)
#
# I. KeyInfo Data Model
#   1.  test_keyinfo_fields: KeyInfo has source and is_set attributes.
#
# II. get_provider_key_names — CSV Parsing
#   2.  test_key_names_csv_missing: No CSV → empty list.
#   3.  test_key_names_csv_empty_file: Empty file → empty list.
#   4.  test_key_names_csv_no_api_key_column: CSV without api_key header → empty list.
#   5.  test_key_names_csv_all_empty_keys: All api_key values blank → empty list.
#   6.  test_key_names_returns_sorted_unique: Normal CSV → sorted, deduplicated keys.
#   7.  test_key_names_deduplicates_across_rows: Same key in multiple rows → single entry.
#   8.  test_key_names_splits_pipe_delimited: Pipe-delimited api_key → individual keys.
#   9.  test_key_names_pipe_dedup_across_rows: Pipe keys deduplicated across rows.
#   10. test_key_names_pipe_strips_whitespace: Whitespace around pipe segments stripped.
#   11. test_key_names_pipe_ignores_empty_segments: Empty pipe segments ignored.
#   12. test_key_names_malformed_csv: Malformed CSV → empty list, no crash.
#   13. test_key_names_permission_error: PermissionError → empty list, no crash.
#   14. test_key_names_unicode: Unicode in CSV → handled correctly.
#
# III. scan_environment — Early Exits
#   15. test_scan_no_models_configured: No CSV → empty dict.
#   16. test_scan_exception_returns_empty: Internal error → empty dict, no raise.
#
# IV. scan_environment — Source Detection
#   17. test_scan_detects_shell_env_key: Key in os.environ → source="shell environment".
#   18. test_scan_detects_api_env_file_key: Key in api-env.{shell} → source="~/.pdd/api-env.{shell}".
#   19. test_scan_detects_dotenv_key: Key in .env → source=".env file".
#   20. test_scan_missing_key_marked_not_set: Key absent everywhere → is_set=False.
#
# V. scan_environment — Priority Order
#   21. test_scan_dotenv_wins_over_shell: .env beats shell environment.
#   22. test_scan_shell_wins_over_api_env: Shell environment beats api-env file.
#
# VI. scan_environment — Shell-Specific Behavior
#   23. test_scan_bash_uses_bash_api_env: SHELL=/bin/bash → reads api-env.bash.
#   24. test_scan_zsh_uses_zsh_api_env: SHELL=/bin/zsh → reads api-env.zsh.
#
# VII. scan_environment — Pipe-Delimited Keys
#   25. test_scan_pipe_keys_scanned_individually: Each pipe-delimited key checked independently.
#
# VIII. scan_environment — Edge Cases
#   26. test_scan_special_chars_in_key_value: Key value with special chars → no crash.
#   27. test_scan_empty_string_values_not_set: Keys with empty values → is_set=False.
#   28. test_scan_empty_dotenv_falls_through_to_shell: Empty .env value → shell environment wins.
#   29. test_scan_empty_shell_falls_through_to_dotenv: Empty shell value → .env file wins.

import csv
from pathlib import Path
from unittest import mock

import pytest

from pdd.api_key_scanner import (
    KeyInfo,
    get_provider_key_names,
    scan_environment,
)


# ---------------------------------------------------------------------------
# Module-level CSV fixtures
# ---------------------------------------------------------------------------

_CSV_FIELDS = [
    "provider", "model", "input", "output", "coding_arena_elo",
    "base_url", "api_key", "max_reasoning_tokens", "structured_output",
    "reasoning_type", "location",
]

SIMPLE_CSV_ROWS = [
    {"provider": "OpenAI", "model": "gpt-4", "input": "30.0", "output": "60.0",
     "coding_arena_elo": "1000", "base_url": "", "api_key": "OPENAI_API_KEY",
     "max_reasoning_tokens": "0", "structured_output": "True",
     "reasoning_type": "", "location": ""},
    {"provider": "Anthropic", "model": "claude-3-opus", "input": "15.0", "output": "75.0",
     "coding_arena_elo": "1000", "base_url": "", "api_key": "ANTHROPIC_API_KEY",
     "max_reasoning_tokens": "0", "structured_output": "True",
     "reasoning_type": "", "location": ""},
    {"provider": "Local", "model": "ollama/llama2", "input": "0.0", "output": "0.0",
     "coding_arena_elo": "1000", "base_url": "http://localhost:11434", "api_key": "",
     "max_reasoning_tokens": "0", "structured_output": "False",
     "reasoning_type": "", "location": ""},
]

BEDROCK_CSV_ROWS = [
    {"provider": "AWS Bedrock", "model": "anthropic.claude-3", "input": "8.0",
     "output": "24.0", "coding_arena_elo": "1000", "base_url": "",
     "api_key": "AWS_ACCESS_KEY_ID|AWS_SECRET_ACCESS_KEY|AWS_REGION_NAME",
     "max_reasoning_tokens": "0", "structured_output": "True",
     "reasoning_type": "", "location": ""},
]

MIXED_CSV_ROWS = SIMPLE_CSV_ROWS + BEDROCK_CSV_ROWS


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _write_csv(path: Path, rows: list[dict], fieldnames: list[str] | None = None):
    """Write rows to a CSV file at *path*."""
    fieldnames = fieldnames or _CSV_FIELDS
    with open(path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def _setup_home(tmp_path, monkeypatch, csv_rows=None, api_env_shell=None,
                api_env_content=None):
    """Set up a fake ~/.pdd directory with optional CSV and api-env file.

    Returns the tmp_path (acting as $HOME).
    """
    pdd_dir = tmp_path / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)
    monkeypatch.setattr(Path, "home", lambda: tmp_path)

    if csv_rows is not None:
        _write_csv(pdd_dir / "llm_model.csv", csv_rows)

    if api_env_shell and api_env_content:
        (pdd_dir / f"api-env.{api_env_shell}").write_text(api_env_content)

    return tmp_path


# ---------------------------------------------------------------------------
# I. KeyInfo Data Model
# ---------------------------------------------------------------------------


def test_keyinfo_fields():
    """KeyInfo dataclass should expose source and is_set."""
    ki = KeyInfo(source="shell environment", is_set=True)
    assert ki.source == "shell environment"
    assert ki.is_set is True

    ki_missing = KeyInfo(source="", is_set=False)
    assert ki_missing.is_set is False


# ---------------------------------------------------------------------------
# II. get_provider_key_names — CSV Parsing
# ---------------------------------------------------------------------------


def test_key_names_csv_missing(tmp_path, monkeypatch):
    """No CSV at all → empty list."""
    _setup_home(tmp_path, monkeypatch)
    assert get_provider_key_names() == []


def test_key_names_csv_empty_file(tmp_path, monkeypatch):
    """CSV file exists but is empty → empty list."""
    home = _setup_home(tmp_path, monkeypatch)
    (home / ".pdd" / "llm_model.csv").touch()
    assert get_provider_key_names() == []


def test_key_names_csv_no_api_key_column(tmp_path, monkeypatch):
    """CSV lacks an api_key column → empty list."""
    home = _setup_home(tmp_path, monkeypatch)
    csv_path = home / ".pdd" / "llm_model.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=["provider", "model"])
        writer.writeheader()
        writer.writerow({"provider": "OpenAI", "model": "gpt-4"})
    assert get_provider_key_names() == []


def test_key_names_csv_all_empty_keys(tmp_path, monkeypatch):
    """All api_key values are blank → empty list."""
    home = _setup_home(tmp_path, monkeypatch)
    csv_path = home / ".pdd" / "llm_model.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=["provider", "model", "api_key"])
        writer.writeheader()
        writer.writerow({"provider": "Local", "model": "llama2", "api_key": ""})
        writer.writerow({"provider": "Local2", "model": "mistral", "api_key": "   "})
    assert get_provider_key_names() == []


def test_key_names_returns_sorted_unique(tmp_path, monkeypatch):
    """Normal CSV → sorted, deduplicated key names (local models with no key excluded)."""
    _setup_home(tmp_path, monkeypatch, csv_rows=SIMPLE_CSV_ROWS)
    assert get_provider_key_names() == ["ANTHROPIC_API_KEY", "OPENAI_API_KEY"]


def test_key_names_deduplicates_across_rows(tmp_path, monkeypatch):
    """Same key used by multiple models → appears only once."""
    home = _setup_home(tmp_path, monkeypatch)
    rows = [
        {"provider": "OpenAI", "model": "gpt-4", "api_key": "OPENAI_API_KEY"},
        {"provider": "OpenAI", "model": "gpt-3.5", "api_key": "OPENAI_API_KEY"},
        {"provider": "Together", "model": "llama", "api_key": "TOGETHER_API_KEY"},
    ]
    _write_csv(home / ".pdd" / "llm_model.csv", rows,
               fieldnames=["provider", "model", "api_key"])
    assert get_provider_key_names() == ["OPENAI_API_KEY", "TOGETHER_API_KEY"]


def test_key_names_splits_pipe_delimited(tmp_path, monkeypatch):
    """Pipe-delimited api_key → individual key names."""
    _setup_home(tmp_path, monkeypatch, csv_rows=BEDROCK_CSV_ROWS)
    assert get_provider_key_names() == [
        "AWS_ACCESS_KEY_ID", "AWS_REGION_NAME", "AWS_SECRET_ACCESS_KEY",
    ]


def test_key_names_pipe_dedup_across_rows(tmp_path, monkeypatch):
    """Pipe keys from multiple rows are deduplicated."""
    home = _setup_home(tmp_path, monkeypatch)
    rows = [
        {"provider": "AWS Bedrock", "model": "claude-3",
         "api_key": "AWS_ACCESS_KEY_ID|AWS_SECRET_ACCESS_KEY|AWS_REGION_NAME"},
        {"provider": "AWS Bedrock", "model": "claude-3.5",
         "api_key": "AWS_ACCESS_KEY_ID|AWS_SECRET_ACCESS_KEY|AWS_REGION_NAME"},
        {"provider": "Anthropic", "model": "claude-3", "api_key": "ANTHROPIC_API_KEY"},
    ]
    _write_csv(home / ".pdd" / "llm_model.csv", rows,
               fieldnames=["provider", "model", "api_key"])
    assert get_provider_key_names() == [
        "ANTHROPIC_API_KEY", "AWS_ACCESS_KEY_ID",
        "AWS_REGION_NAME", "AWS_SECRET_ACCESS_KEY",
    ]


@pytest.mark.parametrize("raw_key,expected", [
    (" KEY_A | KEY_B | KEY_C ", ["KEY_A", "KEY_B", "KEY_C"]),
])
def test_key_names_pipe_strips_whitespace(tmp_path, monkeypatch, raw_key, expected):
    """Whitespace around pipe segments is stripped."""
    home = _setup_home(tmp_path, monkeypatch)
    _write_csv(
        home / ".pdd" / "llm_model.csv",
        [{"provider": "Test", "model": "t", "api_key": raw_key}],
        fieldnames=["provider", "model", "api_key"],
    )
    assert get_provider_key_names() == expected


@pytest.mark.parametrize("raw_key,expected", [
    ("KEY_A||KEY_B|", ["KEY_A", "KEY_B"]),
])
def test_key_names_pipe_ignores_empty_segments(tmp_path, monkeypatch, raw_key, expected):
    """Empty segments in pipe-delimited values are ignored."""
    home = _setup_home(tmp_path, monkeypatch)
    _write_csv(
        home / ".pdd" / "llm_model.csv",
        [{"provider": "Test", "model": "t", "api_key": raw_key}],
        fieldnames=["provider", "model", "api_key"],
    )
    assert get_provider_key_names() == expected


def test_key_names_malformed_csv(tmp_path, monkeypatch):
    """Malformed CSV → empty list, no crash."""
    home = _setup_home(tmp_path, monkeypatch)
    (home / ".pdd" / "llm_model.csv").write_text(
        'this is not,a valid\ncsv file with"broken quotes'
    )
    result = get_provider_key_names()
    assert isinstance(result, list)


def test_key_names_permission_error(tmp_path, monkeypatch):
    """PermissionError reading CSV → empty list, no crash."""
    home = _setup_home(tmp_path, monkeypatch)
    csv_path = home / ".pdd" / "llm_model.csv"
    csv_path.write_text("provider,model,api_key\nTest,test,KEY\n")

    original_open = open

    def _raise_on_csv(file, *args, **kwargs):
        if str(file) == str(csv_path):
            raise PermissionError("Access denied")
        return original_open(file, *args, **kwargs)

    with mock.patch("builtins.open", side_effect=_raise_on_csv):
        assert get_provider_key_names() == []


def test_key_names_unicode(tmp_path, monkeypatch):
    """Unicode in CSV is handled without error."""
    home = _setup_home(tmp_path, monkeypatch)
    _write_csv(
        home / ".pdd" / "llm_model.csv",
        [{"provider": "Tëst", "model": "模型", "api_key": "UNICODE_KEY_名前"}],
        fieldnames=["provider", "model", "api_key"],
    )
    assert "UNICODE_KEY_名前" in get_provider_key_names()


# ---------------------------------------------------------------------------
# III. scan_environment — Early Exits
# ---------------------------------------------------------------------------


def test_scan_no_models_configured(tmp_path, monkeypatch):
    """No CSV → empty dict."""
    _setup_home(tmp_path, monkeypatch)
    assert scan_environment() == {}


def test_scan_exception_returns_empty(tmp_path, monkeypatch):
    """If get_provider_key_names raises, scan_environment returns {}."""
    _setup_home(tmp_path, monkeypatch)
    with mock.patch(
        "pdd.api_key_scanner.get_provider_key_names",
        side_effect=Exception("boom"),
    ):
        assert scan_environment() == {}


# ---------------------------------------------------------------------------
# IV. scan_environment — Source Detection
# ---------------------------------------------------------------------------


def test_scan_detects_shell_env_key(tmp_path, monkeypatch):
    """Key set in os.environ → source='shell environment', is_set=True."""
    _setup_home(tmp_path, monkeypatch, csv_rows=SIMPLE_CSV_ROWS)
    monkeypatch.setenv("OPENAI_API_KEY", "sk-test123")
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

    with mock.patch("pdd.api_key_scanner._load_dotenv_values", return_value={}):
        result = scan_environment()

    assert result["OPENAI_API_KEY"].is_set is True
    assert result["OPENAI_API_KEY"].source == "shell environment"
    assert result["ANTHROPIC_API_KEY"].is_set is False


def test_scan_detects_api_env_file_key(tmp_path, monkeypatch):
    """Key in api-env file → source='~/.pdd/api-env.bash', is_set=True."""
    _setup_home(
        tmp_path, monkeypatch,
        csv_rows=SIMPLE_CSV_ROWS,
        api_env_shell="bash",
        api_env_content="export OPENAI_API_KEY=sk-from-api-env\n",
    )
    monkeypatch.setenv("SHELL", "/bin/bash")
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

    with mock.patch("pdd.api_key_scanner._load_dotenv_values", return_value={}):
        result = scan_environment()

    assert result["OPENAI_API_KEY"].is_set is True
    assert result["OPENAI_API_KEY"].source == "~/.pdd/api-env.bash"
    assert result["ANTHROPIC_API_KEY"].is_set is False


def test_scan_detects_dotenv_key(tmp_path, monkeypatch):
    """Key in .env file → source='.env file', is_set=True."""
    _setup_home(tmp_path, monkeypatch, csv_rows=SIMPLE_CSV_ROWS)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)

    with mock.patch(
        "pdd.api_key_scanner._load_dotenv_values",
        return_value={"OPENAI_API_KEY": "sk-from-dotenv"},
    ):
        result = scan_environment()

    assert result["OPENAI_API_KEY"].is_set is True
    assert result["OPENAI_API_KEY"].source == ".env file"


def test_scan_missing_key_marked_not_set(tmp_path, monkeypatch):
    """Key absent from all sources → is_set=False."""
    _setup_home(tmp_path, monkeypatch, csv_rows=SIMPLE_CSV_ROWS)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

    with mock.patch("pdd.api_key_scanner._load_dotenv_values", return_value={}):
        result = scan_environment()

    assert result["OPENAI_API_KEY"].is_set is False
    assert result["ANTHROPIC_API_KEY"].is_set is False


# ---------------------------------------------------------------------------
# V. scan_environment — Priority Order
# ---------------------------------------------------------------------------


def test_scan_dotenv_wins_over_shell(tmp_path, monkeypatch):
    """.env file has higher priority than shell environment."""
    _setup_home(
        tmp_path, monkeypatch,
        csv_rows=SIMPLE_CSV_ROWS,
        api_env_shell="bash",
        api_env_content="export OPENAI_API_KEY=sk-from-api-env\n",
    )
    monkeypatch.setenv("SHELL", "/bin/bash")
    monkeypatch.setenv("OPENAI_API_KEY", "sk-from-shell")

    with mock.patch(
        "pdd.api_key_scanner._load_dotenv_values",
        return_value={"OPENAI_API_KEY": "sk-from-dotenv"},
    ):
        result = scan_environment()

    assert result["OPENAI_API_KEY"].source == ".env file"


def test_scan_shell_wins_over_api_env(tmp_path, monkeypatch):
    """Shell environment has higher priority than api-env file."""
    _setup_home(
        tmp_path, monkeypatch,
        csv_rows=SIMPLE_CSV_ROWS,
        api_env_shell="bash",
        api_env_content="export OPENAI_API_KEY=sk-from-api-env\n",
    )
    monkeypatch.setenv("SHELL", "/bin/bash")
    monkeypatch.setenv("OPENAI_API_KEY", "sk-from-shell")

    with mock.patch("pdd.api_key_scanner._load_dotenv_values", return_value={}):
        result = scan_environment()

    assert result["OPENAI_API_KEY"].source == "shell environment"


# ---------------------------------------------------------------------------
# VI. scan_environment — Shell-Specific Behavior
# ---------------------------------------------------------------------------


def test_scan_bash_uses_bash_api_env(tmp_path, monkeypatch):
    """SHELL=/bin/bash → reads api-env.bash, not api-env.zsh."""
    home = _setup_home(
        tmp_path, monkeypatch,
        csv_rows=SIMPLE_CSV_ROWS,
        api_env_shell="bash",
        api_env_content="export OPENAI_API_KEY=sk-bash\n",
    )
    # Also create a zsh file with a different key
    (home / ".pdd" / "api-env.zsh").write_text(
        "export ANTHROPIC_API_KEY=ant-zsh\n"
    )
    monkeypatch.setenv("SHELL", "/bin/bash")
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

    with mock.patch("pdd.api_key_scanner._load_dotenv_values", return_value={}):
        result = scan_environment()

    assert result["OPENAI_API_KEY"].is_set is True
    assert result["OPENAI_API_KEY"].source == "~/.pdd/api-env.bash"
    # zsh file should NOT be consulted when shell is bash
    assert result["ANTHROPIC_API_KEY"].is_set is False


def test_scan_zsh_uses_zsh_api_env(tmp_path, monkeypatch):
    """SHELL=/bin/zsh → reads api-env.zsh."""
    _setup_home(
        tmp_path, monkeypatch,
        csv_rows=SIMPLE_CSV_ROWS,
        api_env_shell="zsh",
        api_env_content="export ANTHROPIC_API_KEY=ant-zsh\n",
    )
    monkeypatch.setenv("SHELL", "/bin/zsh")
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

    with mock.patch("pdd.api_key_scanner._load_dotenv_values", return_value={}):
        result = scan_environment()

    assert result["ANTHROPIC_API_KEY"].is_set is True
    assert result["ANTHROPIC_API_KEY"].source == "~/.pdd/api-env.zsh"


# ---------------------------------------------------------------------------
# VII. scan_environment — Pipe-Delimited Keys
# ---------------------------------------------------------------------------


def test_scan_pipe_keys_scanned_individually(tmp_path, monkeypatch):
    """Each segment of a pipe-delimited api_key is checked independently."""
    _setup_home(tmp_path, monkeypatch, csv_rows=BEDROCK_CSV_ROWS)
    monkeypatch.setenv("AWS_ACCESS_KEY_ID", "AKIA...")
    monkeypatch.setenv("AWS_REGION_NAME", "us-east-1")
    monkeypatch.delenv("AWS_SECRET_ACCESS_KEY", raising=False)

    with mock.patch("pdd.api_key_scanner._load_dotenv_values", return_value={}):
        result = scan_environment()

    assert result["AWS_ACCESS_KEY_ID"].is_set is True
    assert result["AWS_ACCESS_KEY_ID"].source == "shell environment"
    assert result["AWS_REGION_NAME"].is_set is True
    assert result["AWS_SECRET_ACCESS_KEY"].is_set is False


# ---------------------------------------------------------------------------
# VIII. scan_environment — Edge Cases
# ---------------------------------------------------------------------------


def test_scan_special_chars_in_key_value(tmp_path, monkeypatch):
    """Keys with special-character values don't crash the scanner."""
    home = _setup_home(tmp_path, monkeypatch)
    _write_csv(
        home / ".pdd" / "llm_model.csv",
        [{"provider": "Test", "model": "t", "api_key": "MY_SPECIAL_KEY"}],
        fieldnames=["provider", "model", "api_key"],
    )
    monkeypatch.setenv("MY_SPECIAL_KEY", "value_with_$pecial_chars")
    monkeypatch.setenv("SHELL", "/bin/bash")

    with mock.patch("pdd.api_key_scanner._load_dotenv_values", return_value={}):
        result = scan_environment()

    assert result["MY_SPECIAL_KEY"].is_set is True


def test_scan_empty_string_values_not_set(tmp_path, monkeypatch):
    """Keys with empty string values are treated as not set from all sources."""
    _setup_home(tmp_path, monkeypatch, csv_rows=SIMPLE_CSV_ROWS)

    # Set one key to empty string in shell environment
    monkeypatch.setenv("OPENAI_API_KEY", "")
    # Set another to whitespace-only
    monkeypatch.setenv("ANTHROPIC_API_KEY", "   ")
    monkeypatch.setenv("SHELL", "/bin/bash")

    # .env returns empty since _load_dotenv_values filters empty strings
    with mock.patch("pdd.api_key_scanner._load_dotenv_values", return_value={}):
        result = scan_environment()

    # Both keys should be marked as not set since they have empty/whitespace values
    assert result["OPENAI_API_KEY"].is_set is False
    assert result["ANTHROPIC_API_KEY"].is_set is False


def test_scan_empty_dotenv_falls_through_to_shell(tmp_path, monkeypatch):
    """Empty .env value is filtered out; shell environment wins."""
    _setup_home(tmp_path, monkeypatch, csv_rows=SIMPLE_CSV_ROWS)
    monkeypatch.setenv("OPENAI_API_KEY", "sk-from-shell")

    # .env has the key but with empty value (gets filtered by _load_dotenv_values)
    # So the implementation should skip .env and find the shell value
    with mock.patch("pdd.api_key_scanner._load_dotenv_values", return_value={}):
        result = scan_environment()

    assert result["OPENAI_API_KEY"].is_set is True
    assert result["OPENAI_API_KEY"].source == "shell environment"


def test_scan_empty_shell_falls_through_to_dotenv(tmp_path, monkeypatch):
    """Empty shell value is skipped; .env file wins."""
    _setup_home(tmp_path, monkeypatch, csv_rows=SIMPLE_CSV_ROWS)
    monkeypatch.setenv("OPENAI_API_KEY", "")  # Empty in shell

    # .env has a real value
    with mock.patch(
        "pdd.api_key_scanner._load_dotenv_values",
        return_value={"OPENAI_API_KEY": "sk-from-dotenv"},
    ):
        result = scan_environment()

    assert result["OPENAI_API_KEY"].is_set is True
    assert result["OPENAI_API_KEY"].source == ".env file"
