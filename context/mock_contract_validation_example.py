"""Runnable example for repository-backed mock-contract validation."""
from pathlib import Path
from tempfile import TemporaryDirectory

from pdd.mock_contract_validation import (
    format_mock_contract_report,
    validate_mock_contracts,
)


def main() -> None:
    """Show a passing test rejected because its mock invents a schema field."""
    with TemporaryDirectory() as directory:
        root = Path(directory)
        schema = root / "context" / "database-schema.md"
        schema.parent.mkdir(parents=True)
        schema.write_text(
            "```\n"
            "user_waitlist/\n"
            "    {uid}/\n"
            "        email: string\n"
            "        status: string\n"
            "```\n",
            encoding="utf-8",
        )

        fixed_code = """
def load_waitlist(ids):
    return query_collection(
        "user_waitlist",
        filters=[("userId", "in", ids)],
    )
"""
        generated_test = """
def test_load_waitlist(mock_query):
    mock_query.return_value = [{"userId": "uid-1"}]
    assert load_waitlist(["uid-1"])
"""
        report = validate_mock_contracts(
            project_root=root,
            production_sources={"backend/reader.py": fixed_code},
            test_sources={"backend/tests/test_reader.py": generated_test},
            baseline_production_sources={"backend/reader.py": ""},
            baseline_test_sources={"backend/tests/test_reader.py": ""},
        )
        print(format_mock_contract_report(report))


if __name__ == "__main__":
    main()
