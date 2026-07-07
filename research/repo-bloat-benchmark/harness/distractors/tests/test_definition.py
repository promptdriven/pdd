"""Tests for the five machine-checked definition conditions."""

import pytest

from harness.distractors.definition import (
    CandidateFile,
    DefinitionChecker,
    imported_modules,
    module_names_for,
)
from harness.distractors.vocabulary import Vocabulary

CORE_SOURCE = '''\
from pkg.storage import load_records

def paginate_ledger_records(records, page_size):
    """Paginate ledger records for the export pipeline."""
    return [records[i:i + page_size] for i in range(0, len(records), page_size)]
'''


@pytest.fixture()
def checker():
    vocabulary = Vocabulary(
        words={"paginate": 3, "ledger": 5, "records": 4, "export": 2, "pipeline": 2}
    )
    return DefinitionChecker.from_core(
        core_files=["src/pkg/pagination.py", "src/pkg/storage.py"],
        core_sources={"src/pkg/pagination.py": CORE_SOURCE},
        target_files=["src/pkg/pagination.py"],
        leak_denylist=["assert slice_page([1, 2, 3], 1, 2) == [3]"],
        vocabulary_floor=0.2,
        core_vocabulary=vocabulary,
    )


def _ok_candidate(**overrides):
    defaults = dict(
        destination_path="src/pkg/ledger_export_helpers.py",
        content=(
            'def format_ledger_records_for_export(records):\n'
            '    """Format ledger records for the export pipeline."""\n'
            "    return [str(r) for r in records]\n"
        ),
        mode="template",
        tier="same-package",
    )
    defaults.update(overrides)
    return CandidateFile(**defaults)


def test_valid_candidate_passes(checker):
    assert checker.check(_ok_candidate()) == []


def test_condition1_core_file_rejected(checker):
    violations = checker.check(
        _ok_candidate(destination_path="src/pkg/storage.py")
    )
    assert any(v.condition == 1 for v in violations)


def test_condition1_core_import_target_rejected(checker):
    # Core imports pkg.storage → a file importable under that name is load-bearing.
    violations = checker.check(
        _ok_candidate(destination_path="other/pkg/storage.py")
    )
    assert any(v.condition in (1, 2) for v in violations)


def test_condition2_conftest_rejected(checker):
    violations = checker.check(_ok_candidate(destination_path="src/pkg/conftest.py"))
    assert any(v.condition == 2 for v in violations)


def test_condition2_dynamic_import_rejected(checker):
    violations = checker.check(
        _ok_candidate(
            content="import importlib\nmod = importlib.import_module('pkg.storage')\n"
        )
    )
    assert any(v.condition == 2 for v in violations)


def test_condition3_unparseable_rejected(checker):
    violations = checker.check(_ok_candidate(content="def broken(:\n  pass\n"))
    assert any(v.condition == 3 for v in violations)


def test_condition3_vocabulary_floor_for_generated(checker):
    violations = checker.check(
        _ok_candidate(
            content=(
                "def zzqx_wobble_frobnicate(xyzzy):\n"
                '    """Completely alien vocabulary."""\n'
                "    return xyzzy\n"
            )
        )
    )
    assert any(v.condition == 3 for v in violations)


def test_condition3_vocabulary_floor_skipped_for_regrow(checker):
    violations = checker.check(
        _ok_candidate(
            mode="regrow",
            source_path="pool/alien.py",
            content=(
                "def zzqx_wobble_frobnicate(xyzzy):\n"
                '    """Alien but verbatim project code."""\n'
                "    return xyzzy\n"
            ),
        )
    )
    assert violations == []


def test_condition4_leakage_rejected(checker):
    violations = checker.check(
        _ok_candidate(
            content=(
                "def helper():\n"
                "    assert slice_page([1, 2, 3], 1, 2) == [3]\n"
            )
        )
    )
    assert any(v.condition == 4 for v in violations)


def test_condition5_path_tell_rejected(checker):
    violations = checker.check(
        _ok_candidate(destination_path="src/pkg/distractor_ledger.py")
    )
    assert any(v.condition == 5 for v in violations)


def test_condition5_content_tell_rejected_for_generated(checker):
    violations = checker.check(
        _ok_candidate(content="# synthetic module\ndef ledger_export_records():\n    pass\n")
    )
    assert any(v.condition == 5 for v in violations)


def test_module_names_and_imports():
    assert "pkg.storage" in module_names_for("src/pkg/storage.py")
    assert "storage" in module_names_for("src/pkg/storage.py")
    names = imported_modules("from pkg.storage import load\nimport os.path\n")
    assert "pkg.storage" in names
    assert "pkg" in names
    assert "os.path" in names and "os" in names
