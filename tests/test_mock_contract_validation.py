"""Regression and contract tests for issue #1939."""
from __future__ import annotations

import json
from pathlib import Path
import subprocess

import pytest

from pdd.mock_contract_validation import (
    MockContractDivergenceError,
    enforce_mock_contracts,
    extract_mock_fields,
    extract_query_fields,
    format_mock_contract_report,
    validate_changed_files,
    validate_mock_contracts,
)


def _write_waitlist_schema(root: Path, *fields: str) -> Path:
    path = root / "context" / "database-schema.md"
    path.parent.mkdir(parents=True, exist_ok=True)
    body = "\n".join(f"        {field}: string" for field in fields)
    path.write_text(
        "# Database Schema\n\n"
        "### user_waitlist\n"
        "```\n"
        "user_waitlist/\n"
        "    {uid}/\n"
        f"{body}\n"
        "```\n",
        encoding="utf-8",
    )
    return path


_BROKEN_CODE = """
def load_waitlist(user_ids):
    return query_collection(
        "user_waitlist",
        filters=[("userId", "in", user_ids)],
    )
"""

_BROKEN_TEST = """
def test_batch_lookup(mock_query):
    mock_query.return_value = [
        {"userId": "uid-1", "email": "person@example.com"},
    ]
    assert load_waitlist(["uid-1"])[0]["userId"] == "uid-1"
"""


def test_issue_1939_mocked_nonexistent_field_is_a_hard_finding(tmp_path: Path) -> None:
    """The exact #4235 shape may not be certified by a green mock."""
    schema = _write_waitlist_schema(tmp_path, "email", "status")

    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"backend/admin_migrations.py": _BROKEN_CODE},
        test_sources={"backend/tests/test_admin_migrations.py": _BROKEN_TEST},
        baseline_production_sources={"backend/admin_migrations.py": "def load_waitlist(ids): return []\n"},
        baseline_test_sources={"backend/tests/test_admin_migrations.py": "def test_old(): pass\n"},
    )

    assert report.status == "diverged"
    assert report.diverged
    assert len(report.findings) == 1
    finding = report.findings[0]
    assert finding.resource == "user_waitlist"
    assert finding.field_name == "userId"
    assert str(schema) in finding.contract_paths[0]
    assert finding.mock_paths == ("backend/tests/test_admin_migrations.py:4",)
    rendered = format_mock_contract_report(report)
    assert "MOCK_CONTRACT_DIVERGENCE" in rendered
    assert "user_waitlist.userId" in rendered
    with pytest.raises(MockContractDivergenceError, match="user_waitlist.userId"):
        enforce_mock_contracts(report)


def test_mock_using_real_schema_field_is_unaffected(tmp_path: Path) -> None:
    _write_waitlist_schema(tmp_path, "email", "status")
    code = _BROKEN_CODE.replace("userId", "email")
    test = _BROKEN_TEST.replace("userId", "email")

    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"backend/reader.py": code},
        test_sources={"backend/tests/test_reader.py": test},
        baseline_production_sources={"backend/reader.py": ""},
        baseline_test_sources={"backend/tests/test_reader.py": ""},
    )

    assert report.status == "clean"
    assert not report.findings
    enforce_mock_contracts(report)


def test_preexisting_query_and_mock_do_not_become_new_failure(tmp_path: Path) -> None:
    _write_waitlist_schema(tmp_path, "email", "status")
    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"reader.py": _BROKEN_CODE},
        test_sources={"tests/test_reader.py": _BROKEN_TEST},
        baseline_production_sources={"reader.py": _BROKEN_CODE},
        baseline_test_sources={"tests/test_reader.py": _BROKEN_TEST},
    )
    assert report.status == "not_applicable"


def test_new_mock_exposes_preexisting_invalid_query(tmp_path: Path) -> None:
    _write_waitlist_schema(tmp_path, "email", "status")
    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"reader.py": _BROKEN_CODE},
        test_sources={"tests/test_reader.py": _BROKEN_TEST + "\nRESOURCE = 'user_waitlist'\n"},
        baseline_production_sources={"reader.py": _BROKEN_CODE},
        baseline_test_sources={"tests/test_reader.py": "def test_old(): pass\n"},
    )
    assert report.status == "diverged"
    assert report.findings[0].field_name == "userId"


def test_additional_occurrence_of_existing_mock_field_is_still_new(tmp_path: Path) -> None:
    """A same-named mock elsewhere in the baseline must not hide a new payload."""
    _write_waitlist_schema(tmp_path, "email", "status")
    baseline_test = "mock_other.return_value = [{'userId': 'unrelated'}]\n"
    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"reader.py": _BROKEN_CODE},
        test_sources={
            "tests/test_reader.py": baseline_test
            + "\nRESOURCE = 'user_waitlist'\n"
            + _BROKEN_TEST
        },
        baseline_production_sources={"reader.py": _BROKEN_CODE},
        baseline_test_sources={"tests/test_reader.py": baseline_test},
    )

    assert report.status == "diverged"


def test_missing_contract_is_inconclusive_not_a_name_heuristic(tmp_path: Path) -> None:
    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"reader.py": _BROKEN_CODE},
        test_sources={"tests/test_reader.py": _BROKEN_TEST},
    )
    assert report.status == "inconclusive"
    assert not report.findings
    assert "no authoritative schema" in report.warnings[0]


def test_independent_sibling_usage_is_corroborating_contract_evidence(tmp_path: Path) -> None:
    _write_waitlist_schema(tmp_path, "email", "status")
    sibling = tmp_path / "backend" / "existing_reader.py"
    sibling.parent.mkdir(parents=True)
    sibling.write_text(
        "def read(values):\n"
        "    return query_collection('user_waitlist', "
        "filters=[('legacyId', 'in', values)])\n",
        encoding="utf-8",
    )
    code = _BROKEN_CODE.replace("userId", "legacyId")
    test = _BROKEN_TEST.replace("userId", "legacyId")

    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"backend/new_reader.py": code},
        test_sources={"backend/tests/test_new_reader.py": test},
    )
    assert report.status == "clean"
    assert any(item.kind == "sibling" for item in report.contracts)


def test_nested_schema_fields_do_not_count_as_top_level_fields(tmp_path: Path) -> None:
    schema = tmp_path / "context" / "database-schema.md"
    schema.parent.mkdir(parents=True)
    schema.write_text(
        "```\n"
        "user_waitlist/\n"
        "    {uid}/\n"
        "        email: string\n"
        "        emailsSent: array<{\n"
        "            templateId: number\n"
        "        }>\n"
        "```\n",
        encoding="utf-8",
    )
    code = _BROKEN_CODE.replace("userId", "templateId")
    test = _BROKEN_TEST.replace("userId", "templateId")
    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"reader.py": code},
        test_sources={"tests/test_reader.py": test},
    )
    assert report.status == "diverged"


def test_qualified_nested_markdown_schema_field_is_real(tmp_path: Path) -> None:
    schema = tmp_path / "context" / "database-schema.md"
    schema.parent.mkdir(parents=True)
    schema.write_text(
        "```\n"
        "user_waitlist/\n"
        "    {uid}/\n"
        "        profile: map\n"
        "            userId: string\n"
        "```\n",
        encoding="utf-8",
    )
    code = _BROKEN_CODE.replace("userId", "profile.userId")
    test = _BROKEN_TEST.replace("userId", "profile.userId")

    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"reader.py": code},
        test_sources={"tests/test_reader.py": test},
    )

    assert report.status == "clean"
    assert "profile.userId" in report.contracts[0].fields


def test_json_schema_contract_is_supported(tmp_path: Path) -> None:
    schema = tmp_path / "schemas" / "collections.schema.json"
    schema.parent.mkdir(parents=True)
    schema.write_text(
        json.dumps(
            {
                "$defs": {
                    "user_waitlist": {
                        "title": "user_waitlist",
                        "type": "object",
                        "properties": {"userId": {"type": "string"}},
                    }
                }
            }
        ),
        encoding="utf-8",
    )
    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"reader.py": _BROKEN_CODE},
        test_sources={"tests/test_reader.py": _BROKEN_TEST},
    )
    assert report.status == "clean"


def test_qualified_nested_json_schema_field_is_real(tmp_path: Path) -> None:
    schema = tmp_path / "schemas" / "collections.schema.json"
    schema.parent.mkdir(parents=True)
    schema.write_text(
        json.dumps(
            {
                "user_waitlist": {
                    "properties": {
                        "profile": {
                            "type": "object",
                            "properties": {"userId": {"type": "string"}},
                        }
                    }
                }
            }
        ),
        encoding="utf-8",
    )
    code = _BROKEN_CODE.replace("userId", "profile.userId")
    test = _BROKEN_TEST.replace("userId", "profile.userId")

    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"reader.py": code},
        test_sources={"tests/test_reader.py": test},
    )

    assert report.status == "clean"
    assert "profile.userId" in report.contracts[0].fields


def test_extractors_only_use_query_and_mock_payload_structure() -> None:
    queries = extract_query_fields(_BROKEN_CODE, "reader.py")
    mocks = extract_mock_fields(_BROKEN_TEST, "test_reader.py")
    assert [(item.resource, item.field_name) for item in queries] == [
        ("user_waitlist", "userId")
    ]
    assert {item.field_name for item in mocks} == {"userId", "email"}


def test_fake_side_effect_function_payload_is_detected() -> None:
    source = """
def fake_query(collection, filters):
    return [{"userId": "uid-1"}]

def test_reader(mock_query):
    mock_query.side_effect = fake_query
"""
    fields = extract_mock_fields(source, "test_reader.py")
    assert [(item.field_name, item.target) for item in fields] == [
        ("userId", "fake_query")
    ]


def test_query_extractor_supports_firestore_chains_and_keyword_filters() -> None:
    source = """
client.collection(collection_name="users").where(
    field_path="email", op_string="==", value="person@example.com"
)
client.collection("users").where(
    filter=FieldFilter(field_path="status", op_string="==", value="active")
)
client.collection("users").filter(FieldFilter("age", ">=", 18))
count_collection(collection_name="users", filters=[("enabled", "==", True)])
query_collection(dynamic_collection, filters=[("ignored", "==", True)])
"""

    fields = extract_query_fields(source, "reader.py")

    assert {(item.resource, item.field_name) for item in fields} == {
        ("users", "age"),
        ("users", "email"),
        ("users", "enabled"),
        ("users", "status"),
    }
    assert all(item.source_path == "reader.py" for item in fields)


def test_extractors_ignore_invalid_or_irrelevant_python() -> None:
    assert extract_query_fields("def broken(", "broken.py") == ()
    assert extract_mock_fields("def broken(", "test_broken.py") == ()
    assert extract_query_fields("query_collection(name, filters=None)") == ()
    assert extract_mock_fields("payload = {'ordinary': 'data'}") == ()


def test_mock_extractor_supports_annotations_factories_and_patch_object() -> None:
    source = """
def fake_lookup():
    return [{"sideEffectId": "one"}]

mock_lookup: object = MagicMock(return_value=[{"annotatedId": "two"}])
direct = AsyncMock(side_effect=lambda: [{"asyncId": "three"}])
context = patch.object(service, "lookup", side_effect=fake_lookup)
ordinary = {"ignored": "four"}
"""

    fields = extract_mock_fields(source, "tests/test_reader.py")

    assert {item.field_name for item in fields} == {
        "annotatedId",
        "asyncId",
        "sideEffectId",
    }
    assert "ignored" not in {item.field_name for item in fields}


def test_root_json_schema_fields_and_list_shape_are_supported(tmp_path: Path) -> None:
    (tmp_path / "api-schema.json").write_text(
        json.dumps(
            [
                {
                    "name": "user_waitlist",
                    "fields": {"userId": {"type": "string"}},
                }
            ]
        ),
        encoding="utf-8",
    )
    context = tmp_path / "context"
    context.mkdir()
    (context / "broken-schema.json").write_text("{invalid", encoding="utf-8")

    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"reader.py": _BROKEN_CODE},
        test_sources={"tests/test_reader.py": _BROKEN_TEST},
    )

    assert report.status == "clean"
    assert report.contracts[0].fields == frozenset({"userId"})


def test_independent_writer_is_corroborating_contract_evidence(tmp_path: Path) -> None:
    _write_waitlist_schema(tmp_path, "email", "status")
    sibling = tmp_path / "backend" / "existing_writer.py"
    sibling.parent.mkdir(parents=True)
    sibling.write_text(
        "set_document(collection_name='user_waitlist', document_id='uid-1', "
        "data={'legacyId': 'uid-1'})\n",
        encoding="utf-8",
    )
    code = _BROKEN_CODE.replace("userId", "legacyId")
    test = _BROKEN_TEST.replace("userId", "legacyId")

    report = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"backend/new_reader.py": code},
        test_sources={"backend/tests/test_new_reader.py": test},
    )

    assert report.status == "clean"
    sibling_contract = next(item for item in report.contracts if item.kind == "sibling")
    assert sibling_contract.fields == frozenset({"legacyId"})


def test_validate_changed_files_uses_git_baseline(tmp_path: Path) -> None:
    _write_waitlist_schema(tmp_path, "email", "status")
    code = tmp_path / "backend" / "reader.py"
    test = tmp_path / "backend" / "tests" / "test_reader.py"
    code.parent.mkdir(parents=True)
    test.parent.mkdir(parents=True)
    code.write_text("def load(ids): return []\n", encoding="utf-8")
    test.write_text("def test_old(): pass\n", encoding="utf-8")
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "backend"], cwd=tmp_path, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=PDD Test",
            "-c",
            "user.email=pdd-test@example.com",
            "commit",
            "-qm",
            "baseline",
        ],
        cwd=tmp_path,
        check=True,
    )
    code.write_text(_BROKEN_CODE, encoding="utf-8")
    test.write_text(_BROKEN_TEST, encoding="utf-8")

    report = validate_changed_files(
        project_root=tmp_path,
        changed_files=[str(code), "backend/tests/test_reader.py", "README.md", "missing.py"],
        baseline_ref="HEAD",
    )

    assert report.status == "diverged"
    assert report.findings[0].field_name == "userId"


def test_changed_file_loader_checks_new_mock_for_unchanged_query(tmp_path: Path) -> None:
    """Agentic test-only edits cannot bypass an unchanged invalid reader."""
    _write_waitlist_schema(tmp_path, "email", "status")
    code = tmp_path / "backend" / "reader.py"
    test = tmp_path / "backend" / "tests" / "test_reader.py"
    code.parent.mkdir(parents=True)
    test.parent.mkdir(parents=True)
    code.write_text(_BROKEN_CODE, encoding="utf-8")
    test.write_text(
        "RESOURCE = 'user_waitlist'\ndef test_old(): pass\n", encoding="utf-8"
    )
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "backend"], cwd=tmp_path, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=PDD Test",
            "-c",
            "user.email=pdd-test@example.com",
            "commit",
            "-qm",
            "baseline",
        ],
        cwd=tmp_path,
        check=True,
    )
    test.write_text(
        "RESOURCE = 'user_waitlist'\n" + _BROKEN_TEST, encoding="utf-8"
    )

    report = validate_changed_files(
        project_root=tmp_path,
        changed_files=["backend/tests/test_reader.py"],
        baseline_ref="HEAD",
    )

    assert report.status == "diverged"
    assert report.findings[0].code_path == "backend/reader.py"


def test_changed_file_loader_ignores_paths_outside_project(tmp_path: Path) -> None:
    outside = tmp_path.parent / f"{tmp_path.name}-outside.py"
    outside.write_text(_BROKEN_CODE, encoding="utf-8")
    try:
        report = validate_changed_files(
            project_root=tmp_path,
            changed_files=[str(outside), "not-created.py"],
        )
    finally:
        outside.unlink()

    assert report.status == "not_applicable"
    assert format_mock_contract_report(report).startswith("Mock-contract validation: not applicable")


def test_report_formatter_covers_clean_and_inconclusive_results(tmp_path: Path) -> None:
    not_applicable = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"reader.py": ""},
        test_sources={"tests/test_reader.py": ""},
    )
    assert "not applicable" in format_mock_contract_report(not_applicable)

    _write_waitlist_schema(tmp_path, "userId")
    clean = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"reader.py": _BROKEN_CODE},
        test_sources={"tests/test_reader.py": _BROKEN_TEST},
    )
    assert "clean" in format_mock_contract_report(clean)

    (tmp_path / "context" / "database-schema.md").unlink()

    inconclusive = validate_mock_contracts(
        project_root=tmp_path,
        production_sources={"reader.py": _BROKEN_CODE},
        test_sources={"tests/test_reader.py": _BROKEN_TEST},
    )
    assert "inconclusive" in format_mock_contract_report(inconclusive)
    assert "no authoritative schema" in format_mock_contract_report(inconclusive)
