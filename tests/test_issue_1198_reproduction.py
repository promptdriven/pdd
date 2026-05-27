"""Reproduction tests for issue #1198.

`.pddrc` silently ignores unknown keys; no schema validation.

These tests assert the CORRECT (expected) behavior: a warning should be
emitted when `_load_pddrc_config()` encounters an unrecognized key. They
will FAIL against the current buggy code path in
`pdd/construct_paths.py:_load_pddrc_config`, which performs only minimal
structural validation (root-is-dict + `contexts` key present) and silently
accepts every other key.

Once the fix lands (a `_validate_pddrc_keys()` helper that emits
`logging.warning()` and/or `warnings.warn()` for each unknown key at root,
per-context, and `defaults` levels), these tests should pass and remain
as permanent regression guards.

Issue: https://github.com/promptdriven/pdd/issues/1198
"""

from __future__ import annotations

import logging
import warnings
from pathlib import Path

import pytest

from pdd.construct_paths import _load_pddrc_config


def _write_pddrc(tmp_path: Path, body: str) -> Path:
    pddrc = tmp_path / ".pddrc"
    pddrc.write_text(body, encoding="utf-8")
    return pddrc


def _warning_signals(caplog, recorded_warnings, key: str) -> bool:
    """Return True if any captured logging record or Python warning mentions `key`."""
    if any(key in rec.getMessage() for rec in caplog.records):
        return True
    if any(key in str(w.message) for w in recorded_warnings):
        return True
    return False


def test_unknown_root_key_emits_warning(tmp_path, caplog):
    """An unknown top-level key in .pddrc must surface as a warning, not be silently dropped."""
    pddrc = _write_pddrc(
        tmp_path,
        """
contexts:
  default:
    defaults:
      generate_output_path: pdd/
typo_at_root: should_warn
""",
    )

    caplog.set_level(logging.WARNING)
    with warnings.catch_warnings(record=True) as recorded:
        warnings.simplefilter("always")
        config = _load_pddrc_config(pddrc)

    # Loading must still succeed (warn-not-fail), but the user must be told.
    assert "contexts" in config
    assert _warning_signals(caplog, recorded, "typo_at_root"), (
        "Expected a warning naming the unknown root key 'typo_at_root'; "
        "current code silently accepts it (issue #1198)."
    )


def test_unknown_defaults_key_emits_warning(tmp_path, caplog):
    """An unknown key inside a context's `defaults` block must produce a warning."""
    pddrc = _write_pddrc(
        tmp_path,
        """
contexts:
  default:
    defaults:
      generate_output_path: pdd/
      bogus_unknown_key: value
""",
    )

    caplog.set_level(logging.WARNING)
    with warnings.catch_warnings(record=True) as recorded:
        warnings.simplefilter("always")
        _load_pddrc_config(pddrc)

    assert _warning_signals(caplog, recorded, "bogus_unknown_key"), (
        "Expected a warning naming the unknown defaults key 'bogus_unknown_key'; "
        "current code silently accepts it (issue #1198)."
    )


def test_unknown_per_context_key_emits_warning(tmp_path, caplog):
    """An unknown key at the per-context level (sibling of `paths`/`defaults`) must warn."""
    pddrc = _write_pddrc(
        tmp_path,
        """
contexts:
  default:
    paths: ["**/*"]
    defaults:
      generate_output_path: pdd/
    bogus_context_key: should_warn
""",
    )

    caplog.set_level(logging.WARNING)
    with warnings.catch_warnings(record=True) as recorded:
        warnings.simplefilter("always")
        _load_pddrc_config(pddrc)

    assert _warning_signals(caplog, recorded, "bogus_context_key"), (
        "Expected a warning naming the unknown per-context key 'bogus_context_key'; "
        "current code silently accepts it (issue #1198)."
    )


def test_valid_config_emits_no_warning(tmp_path, caplog):
    """A fully-valid .pddrc must produce zero unknown-key warnings (no false positives)."""
    pddrc = _write_pddrc(
        tmp_path,
        """
version: 1
contexts:
  default:
    paths: ["**/*"]
    defaults:
      generate_output_path: pdd/
      test_output_path: tests/
      example_output_path: context/
      prompts_dir: pdd/prompts/
      default_language: python
      target_coverage: 90.0
      strength: 0.85
      temperature: 0.0
      budget: 10.0
      max_attempts: 3
""",
    )

    caplog.set_level(logging.WARNING)
    with warnings.catch_warnings(record=True) as recorded:
        warnings.simplefilter("always")
        _load_pddrc_config(pddrc)

    unknown_signals = [
        rec.getMessage() for rec in caplog.records if "unknown key" in rec.getMessage().lower()
    ] + [str(w.message) for w in recorded if "unknown key" in str(w.message).lower()]
    assert not unknown_signals, (
        f"A schema-valid .pddrc must not produce unknown-key warnings, got: {unknown_signals}"
    )


def test_load_does_not_raise_on_unknown_keys(tmp_path):
    """Backward compat: unknown keys must warn-not-fail; loading must still return a dict."""
    pddrc = _write_pddrc(
        tmp_path,
        """
contexts:
  default:
    defaults:
      generate_output_path: pdd/
unknown_thing: x
""",
    )
    config = _load_pddrc_config(pddrc)
    assert isinstance(config, dict)
    assert "contexts" in config


# ---------------------------------------------------------------------------
# Step 9 additions per Step 8's test plan (tests 6 and 7).
# ---------------------------------------------------------------------------


def _all_warning_messages(caplog, recorded_warnings) -> list[str]:
    return [rec.getMessage() for rec in caplog.records] + [
        str(w.message) for w in recorded_warnings
    ]


def test_warning_message_format_names_key_path_and_setup(tmp_path, caplog):
    """The warning text must name the offending key, its dotted path, and the
    'pdd setup' remediation pointer — the user-facing contract described in
    issue #1198. Without all three, users cannot act on the warning.
    """
    pddrc = _write_pddrc(
        tmp_path,
        """
contexts:
  default:
    defaults:
      generate_output_path: pdd/
      bogus_unknown_key: value
""",
    )

    caplog.set_level(logging.WARNING)
    with warnings.catch_warnings(record=True) as recorded:
        warnings.simplefilter("always")
        _load_pddrc_config(pddrc)

    messages = _all_warning_messages(caplog, recorded)
    matching = [m for m in messages if "bogus_unknown_key" in m]
    assert matching, (
        f"Expected a warning mentioning 'bogus_unknown_key'; got messages: {messages}"
    )

    combined = "\n".join(matching)
    # Key name present.
    assert "bogus_unknown_key" in combined
    # Dotted path that locates the key inside the parsed structure.
    # Per Step 6/8 spec: dot-joined path from root to the offending key.
    assert "contexts.default.defaults" in combined, (
        f"Warning must include the dotted path 'contexts.default.defaults'; got: {combined!r}"
    )
    # Remediation pointer.
    assert "pdd setup" in combined, (
        f"Warning must point users to 'pdd setup' for regeneration; got: {combined!r}"
    )


def test_multiple_unknown_keys_each_warn(tmp_path, caplog):
    """Aggregation: every unknown key should produce its own warning — the
    validator must not stop at the first violation. Issue #1198 explicitly
    asks users to be told about ALL stale keys so they can clean up the file
    in one pass.
    """
    pddrc = _write_pddrc(
        tmp_path,
        """
typo_at_root: x
also_bad: y
contexts:
  default:
    defaults:
      generate_output_path: pdd/
      bogus_unknown_key: 1
      another_typo: 2
""",
    )

    caplog.set_level(logging.WARNING)
    with warnings.catch_warnings(record=True) as recorded:
        warnings.simplefilter("always")
        _load_pddrc_config(pddrc)

    messages = _all_warning_messages(caplog, recorded)
    combined = "\n".join(messages)
    for expected_key in ("typo_at_root", "also_bad", "bogus_unknown_key", "another_typo"):
        assert expected_key in combined, (
            f"Expected a warning mentioning unknown key {expected_key!r}; "
            f"validator must report ALL unknown keys, not just the first. "
            f"Got messages: {messages}"
        )


if __name__ == "__main__":  # pragma: no cover - manual smoke run
    pytest.main([__file__, "-vv"])
