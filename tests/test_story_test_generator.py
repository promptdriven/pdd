"""Tests for deterministic story-to-pytest generation (#1700)."""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd.commands.generate import test as test_cmd
from pdd.story_test_generator import (
    generate_story_test,
    parse_story_test_spec,
    render_story_test,
)
from pdd.user_story_tests import _story_content_hash


def _write_story_contract(root: Path) -> Path:
    stories = root / "user_stories"
    contracts = stories / "contracts"
    story = stories / "story__checkout_total.md"
    story.parent.mkdir(parents=True, exist_ok=True)
    contracts.mkdir(parents=True, exist_ok=True)
    story.write_text(
        "<!-- pdd-story-prompts: prompts/checkout_python.prompt -->\n"
        "## Story\n\nAs a shopper, I see the correct checkout total.\n",
        encoding="utf-8",
    )
    (contracts / "checkout_total.contract.md").write_text(
        "<!-- pdd-story-contract derived-from-story=\"../story__checkout_total.md\" "
        "story-hash=\"<auto>\" issue-ref=\"local\" -->\n\n"
        "# Contract: checkout total\n\n"
        "## Covers\n\n"
        "- R1: checkout total\n\n"
        "## Entry Point\n\n"
        "- module: checkout_app\n"
        "- callable: checkout_total\n"
        "- args: [1, 2]\n"
        "- kwargs: {}\n\n"
        "## Seams\n\n"
        "- checkout_app.TAX_RATE = 0\n\n"
        "## Oracle\n\n"
        "- result[\"total\"] == 3\n\n"
        "## Negative Cases\n\n"
        "- result[\"charged_twice\"] is False\n",
        encoding="utf-8",
    )
    return story


def _write_app(root: Path, total_expr: str = "subtotal + TAX_RATE") -> None:
    (root / "checkout_app.py").write_text(
        "TAX_RATE = 99\n\n"
        "def checkout_total(a, b):\n"
        "    subtotal = a + b\n"
        f"    return {{\"total\": {total_expr}, \"charged_twice\": False}}\n",
        encoding="utf-8",
    )


def test_parse_story_test_spec_reads_entrypoint_and_hash(tmp_path: Path):
    story = _write_story_contract(tmp_path)
    spec = parse_story_test_spec(story)
    assert spec.story_id == "checkout_total"
    assert spec.story_hash == _story_content_hash(story.read_text(encoding="utf-8"))
    assert spec.module == "checkout_app"
    assert spec.callable_name == "checkout_total"
    assert spec.rule_ids == ("R1",)


@pytest.mark.parametrize(
    ("rule_id", "function_segment"),
    [
        ("R1a", "R1A"),
        ("R-1A", "R_1A"),
        ("RULE1A", "RULE1A"),
        ("RULE-1A", "RULE_1A"),
    ],
)
def test_story_rule_grammar_renders_valid_python(
    tmp_path: Path,
    rule_id: str,
    function_segment: str,
):
    story = _write_story_contract(tmp_path)
    contract = tmp_path / "user_stories" / "contracts" / "checkout_total.contract.md"
    contract.write_text(
        contract.read_text(encoding="utf-8").replace(
            "- R1: checkout total", f"- {rule_id}: specialized checkout total"
        ),
        encoding="utf-8",
    )
    spec = parse_story_test_spec(story)
    assert spec.rule_ids == (rule_id.upper(),)
    rendered = render_story_test(spec)
    compile(rendered, "<generated-story-test>", "exec")
    assert f"RULE_IDS = ({rule_id.upper()!r},)" in rendered
    assert f"test_story_checkout_total_{function_segment}_oracle_1" in rendered


def test_generate_story_test_is_deterministic_and_marks_story(tmp_path: Path):
    story = _write_story_contract(tmp_path)
    output = tmp_path / "tests" / "test_story_checkout_total.py"
    first = generate_story_test(story, output)
    first_text = output.read_text(encoding="utf-8")
    second = generate_story_test(story, output)
    assert second.output_path == first.output_path
    assert output.read_text(encoding="utf-8") == first_text
    assert '@pytest.mark.story(story_id=STORY_ID, story_hash=STORY_HASH)' in first_text
    assert "def test_story_checkout_total_R1_oracle_1" in first_text


def test_generated_story_test_passes_and_fails_on_seeded_violation(tmp_path: Path):
    story = _write_story_contract(tmp_path)
    _write_app(tmp_path)
    output = tmp_path / "tests" / "test_story_checkout_total.py"
    generate_story_test(story, output)

    passing = subprocess.run(
        [sys.executable, "-m", "pytest", str(output), "-q"],
        cwd=tmp_path,
        text=True,
        capture_output=True,
        check=False,
    )
    assert passing.returncode == 0, passing.stdout + passing.stderr

    _write_app(tmp_path, total_expr="subtotal + 1")
    failing = subprocess.run(
        [sys.executable, "-m", "pytest", str(output), "-q"],
        cwd=tmp_path,
        text=True,
        capture_output=True,
        check=False,
    )
    assert failing.returncode != 0
    assert "test_story_checkout_total_R1_oracle_1" in failing.stdout


def _run_generated_test(tmp_path: Path, output: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-m", "pytest", str(output), "-q"],
        cwd=tmp_path,
        text=True,
        capture_output=True,
        check=False,
    )


def test_pdd_test_from_story_cli_writes_generated_test(tmp_path: Path):
    story = _write_story_contract(tmp_path)
    _write_app(tmp_path)
    output = tmp_path / "tests" / "test_story_checkout_total.py"
    runner = CliRunner()
    result = runner.invoke(
        test_cmd,
        ["--from-story", str(story), "--output", str(output)],
        obj={"quiet": True, "verbose": False},
    )
    assert result.exit_code == 0, result.output
    assert output.is_file()
    text = output.read_text(encoding="utf-8")
    assert "STORY_HASH" in text

    # Shape: the contract declares ## Entry Point, so the CLI must emit the
    # *behavioral* template — it resolves the entry-point callable and asserts
    # the contract's oracle expressions over the live `result`, not a text pin.
    assert "ENTRY_MODULE = 'checkout_app'" in text
    assert "ENTRY_CALLABLE = 'checkout_total'" in text
    assert 'result["total"] == 3' in text
    assert 'result["charged_twice"] is False' in text
    assert "STORY_ID = 'checkout_total'" in text
    assert "@pytest.mark.story(story_id=STORY_ID, story_hash=STORY_HASH)" in text
    assert "_bundle_hash" not in text  # text-pin template marker must be absent

    # Behavior: the generated tests execute the fixture app (applying the
    # ## Seams patch — without it the total would be 102, not 3) and pass.
    passing = _run_generated_test(tmp_path, output)
    assert passing.returncode == 0, passing.stdout + passing.stderr
    assert "2 passed" in passing.stdout  # one oracle + one negative-case test

    # ...and go red, WITHOUT regeneration, when the app's behavior regresses.
    # This is what proves the file is a live oracle rather than a text pin or
    # a set of trivially-true assertions.
    _write_app(tmp_path, total_expr="subtotal + 1")
    failing = _run_generated_test(tmp_path, output)
    assert failing.returncode != 0
    assert "test_story_checkout_total_R1_oracle_1" in failing.stdout
    assert "1 failed" in failing.stdout


def test_pdd_test_from_story_cli_without_entry_point_writes_text_pin(tmp_path: Path):
    """The same CLI path, given a contract WITHOUT ## Entry Point, must fall
    back to the text-pin template: no import of the app, hash + clause pins."""
    stories = tmp_path / "user_stories"
    contracts = stories / "contracts"
    contracts.mkdir(parents=True, exist_ok=True)
    story = stories / "story__checkout_refund.md"
    story.write_text(
        "# User Story: refund\n\n## Story\n\n"
        "A shopper can refund an eligible checkout.\n",
        encoding="utf-8",
    )
    (contracts / "checkout_refund.contract.md").write_text(
        "## Covers\n\n- R1\n\n"
        "## Oracle\n\n- Eligible checkout refunds are accepted.\n\n"
        "## Negative Cases\n\n- Ineligible checkout refunds are rejected.\n",
        encoding="utf-8",
    )
    output = tmp_path / "tests" / "test_story_checkout_refund.py"
    runner = CliRunner()
    result = runner.invoke(
        test_cmd,
        ["--from-story", str(story), "--output", str(output)],
        obj={"quiet": True, "verbose": False},
    )
    assert result.exit_code == 0, result.output
    assert output.is_file()
    text = output.read_text(encoding="utf-8")
    assert "checkout_app" not in text  # no entry-point import in text-pin mode
    assert "import importlib" not in text
    assert "_bundle_hash() == PDD_STORY_HASH" in text  # pins the bundle hash
    assert "Eligible checkout refunds are accepted." in text  # pins clauses
    assert "Ineligible checkout refunds are rejected." in text
    assert "@pytest.mark.story(story_id=PDD_STORY_ID)" in text

    # The text-pin tests run green against the current story bundle...
    passing = _run_generated_test(tmp_path, output)
    assert passing.returncode == 0, passing.stdout + passing.stderr
    assert "2 passed" in passing.stdout

    # ...and go stale-red when the story text changes under the pinned hash.
    story.write_text(
        story.read_text(encoding="utf-8") + "\nRefunds are idempotent.\n",
        encoding="utf-8",
    )
    stale = _run_generated_test(tmp_path, output)
    assert stale.returncode != 0


def test_from_story_requires_machine_readable_entrypoint(tmp_path: Path):
    story = _write_story_contract(tmp_path)
    contract = tmp_path / "user_stories" / "contracts" / "checkout_total.contract.md"
    contract.write_text("## Oracle\n\n- result is not None\n", encoding="utf-8")
    with pytest.raises(ValueError, match="Entry Point"):
        generate_story_test(story, tmp_path / "tests" / "test_story.py")
