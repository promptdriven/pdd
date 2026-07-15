"""Repository dogfood invariants independent of PDD sync command code."""

from __future__ import annotations

import ast

from scripts.manual_repository_sync import (
    _clean_reason,
    _python_signature,
    _render_interface_block,
)
from scripts.repository_sync_audit import (
    _architecture_graph_findings,
    _typescript_exports,
    audit,
    parse_prompt_metadata,
)


def test_repository_prompt_program_is_fully_accounted_and_aligned() -> None:
    counts, findings = audit()
    assert counts["expected_managed_prompts"] > 0
    assert counts["fingerprints"] == 44
    assert counts["fingerprints_fresh_minimum"] == 0
    assert counts["fingerprints_stale_or_unknown"] == 44
    assert not findings, "repository sync audit failed:\n" + "\n".join(
        f"[{item.category}] {item.subject}: {item.detail}" for item in findings
    )


def test_graph_audit_rejects_cycles_and_non_dependency_first_priorities() -> None:
    entries = [
        {"filename": "a.prompt", "dependencies": ["b.prompt"], "priority": 1},
        {"filename": "b.prompt", "dependencies": ["a.prompt"], "priority": 2},
    ]
    findings = _architecture_graph_findings(entries)
    assert any(item.category == "architecture-cycle" for item in findings)
    assert any(item.category == "architecture-priority" for item in findings)


def test_typescript_export_scanner_understands_arrow_exports(tmp_path) -> None:
    source = tmp_path / "icons.tsx"
    source.write_text(
        "export const Icon = (props: React.SVGProps<SVGSVGElement>) => (<svg {...props} />);\n"
        "export interface IconProps { title?: string; }\n",
        encoding="utf-8",
    )
    functions, types = _typescript_exports(source)
    assert functions["Icon"][0] == "(props:React.SVGProps<SVGSVGElement>)"
    assert "IconProps" in types


def test_interface_refresh_preserves_prompt_return_for_unannotated_code() -> None:
    function = ast.parse("def flush():\n    pass\n").body[0]
    signature, returns = _python_signature(function, "None")
    assert signature == "() -> None"
    assert returns == "None"


def test_reason_cleaning_preserves_identifier_underscores() -> None:
    assert "PDD_CLOUD_URL" in _clean_reason("Routes PDD_CLOUD_URL requests safely")


def test_llm_interface_metadata_is_parseable_and_runtime_format_safe(tmp_path) -> None:
    prompt = tmp_path / "worker_LLM.prompt"
    interface = {"type": "config", "config": {"keys": []}}
    block = _render_interface_block(prompt, interface)
    prompt.write_text(block + "\n\n% Input: {payload}\n", encoding="utf-8")

    assert block.format() == block.replace("{{", "{").replace("}}", "}")
    assert parse_prompt_metadata(prompt).interface == interface
