"""
Reproduction tests for issue #1060: `pdd sync` pollutes root architecture.json
with entries from bundled-sample arch files and from nested architecture files.

Two-layer bug:
  Layer 1 (discovery): find_architecture_for_project() returns bundled-sample
    arch files (under examples/, example_project/, example_workspace/, staging/).
  Layer 2 (write routing): _apply_architecture_corrections() writes the combined
    in-memory architecture list back to the primary (root) arch path, flattening
    nested arch entries into root.

These tests must FAIL on current main and PASS after the fix.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from pdd.agentic_sync import _apply_architecture_corrections
from pdd.architecture_include_validation import list_validate_arch_include_warnings
from pdd.architecture_registry import (
    find_architecture_for_project,
    load_combined_architecture_data,
)


def _write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2), encoding="utf-8")


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# AC #1: root scan with bundled examples — root arch must not gain example modules
# ---------------------------------------------------------------------------


def test_ac1_discovery_skips_bundled_examples(tmp_path: Path) -> None:
    """find_architecture_for_project must skip bundled-sample top-level trees by default."""
    (tmp_path / ".git").mkdir()
    _write_json(
        tmp_path / "architecture.json",
        [{"filename": "root_mod_python.prompt", "dependencies": []}],
    )
    _write_json(
        tmp_path / "examples" / "arch" / "architecture.json",
        [{"filename": "order_api_Python.prompt", "dependencies": []}],
    )
    _write_json(
        tmp_path / "examples" / "template_example" / "architecture.json",
        [{"filename": "cli_python.prompt", "dependencies": []}],
    )

    arch_files = find_architecture_for_project(tmp_path)
    rel = sorted(str(p.relative_to(tmp_path).as_posix()) for p in arch_files)
    assert rel == ["architecture.json"], (
        f"Bundled-sample arch files leaked into discovery: {rel}"
    )


def test_ac1_combined_data_excludes_examples(tmp_path: Path) -> None:
    """load_combined_architecture_data must exclude bundled examples by default."""
    (tmp_path / ".git").mkdir()
    _write_json(
        tmp_path / "architecture.json",
        [{"filename": "root_mod_python.prompt", "dependencies": []}],
    )
    _write_json(
        tmp_path / "examples" / "arch" / "architecture.json",
        [{"filename": "order_api_Python.prompt", "dependencies": []}],
    )

    combined, _ = load_combined_architecture_data(tmp_path)
    assert combined is not None
    filenames = {entry.get("filename") for entry in combined}
    assert filenames == {"root_mod_python.prompt"}, (
        f"Combined data leaked example modules: {filenames}"
    )


# ---------------------------------------------------------------------------
# AC #2: nested non-sample arch correction — write goes to owning file, not root
# ---------------------------------------------------------------------------


def test_ac2_nested_correction_writes_to_owning_file(tmp_path: Path) -> None:
    """A correction for a module in services/api/architecture.json must update only
    that nested file. Root architecture.json must not be modified."""
    (tmp_path / ".git").mkdir()
    root_arch = tmp_path / "architecture.json"
    nested_arch = tmp_path / "services" / "api" / "architecture.json"

    root_data = [{"filename": "root_mod_python.prompt", "dependencies": []}]
    nested_data = [
        {"filename": "api_python.prompt", "dependencies": ["models_python.prompt"]},
        {"filename": "models_python.prompt", "dependencies": []},
    ]
    _write_json(root_arch, root_data)
    _write_json(nested_arch, nested_data)

    root_before = _read_json(root_arch)
    corrections = [
        {
            "filename": "api_python.prompt",
            "dependencies": ["models_python.prompt", "auth_python.prompt"],
        }
    ]
    _apply_architecture_corrections(tmp_path, corrections, quiet=True)

    root_after = _read_json(root_arch)
    nested_after = _read_json(nested_arch)

    assert root_after == root_before, (
        "Root architecture.json was mutated by a nested correction; "
        f"before={root_before!r} after={root_after!r}"
    )
    nested_by_fn = {e["filename"]: e for e in nested_after}
    assert nested_by_fn["api_python.prompt"]["dependencies"] == [
        "models_python.prompt",
        "auth_python.prompt",
    ]


# ---------------------------------------------------------------------------
# AC #3: root correction with nested arch present — only root changes
# ---------------------------------------------------------------------------


def test_ac3_root_correction_does_not_touch_nested(tmp_path: Path) -> None:
    """A correction for a root module must update only root architecture.json,
    leaving nested arch files unchanged."""
    (tmp_path / ".git").mkdir()
    root_arch = tmp_path / "architecture.json"
    nested_arch = tmp_path / "services" / "api" / "architecture.json"

    _write_json(
        root_arch,
        [
            {"filename": "root_mod_python.prompt", "dependencies": []},
            {"filename": "helper_python.prompt", "dependencies": []},
        ],
    )
    _write_json(
        nested_arch,
        [{"filename": "api_python.prompt", "dependencies": []}],
    )

    nested_before = _read_json(nested_arch)
    corrections = [
        {
            "filename": "root_mod_python.prompt",
            "dependencies": ["helper_python.prompt"],
        }
    ]
    _apply_architecture_corrections(tmp_path, corrections, quiet=True)

    root_after = _read_json(root_arch)
    nested_after = _read_json(nested_arch)

    assert nested_after == nested_before, (
        "Nested architecture.json was mutated by a root correction"
    )
    root_by_fn = {e["filename"]: e for e in root_after}
    assert root_by_fn["root_mod_python.prompt"]["dependencies"] == [
        "helper_python.prompt"
    ]
    # Critical: the root file must not have gained the nested module.
    assert "api_python.prompt" not in root_by_fn


# ---------------------------------------------------------------------------
# AC #4: ambiguous duplicate filename — skip + warn, no write
# ---------------------------------------------------------------------------


def test_ac4_ambiguous_correction_is_skipped(tmp_path: Path) -> None:
    """When the same filename appears in two arch files, the correction must be
    skipped (no write to either file)."""
    (tmp_path / ".git").mkdir()
    root_arch = tmp_path / "architecture.json"
    nested_arch = tmp_path / "services" / "api" / "architecture.json"

    shared_entry = {"filename": "auth_python.prompt", "dependencies": []}
    _write_json(root_arch, [shared_entry])
    _write_json(nested_arch, [shared_entry])

    root_before = _read_json(root_arch)
    nested_before = _read_json(nested_arch)

    corrections = [
        {
            "filename": "auth_python.prompt",
            "dependencies": ["new_dep_python.prompt"],
        }
    ]
    _apply_architecture_corrections(tmp_path, corrections, quiet=True)

    assert _read_json(root_arch) == root_before, (
        "Root arch was mutated despite ambiguous filename"
    )
    assert _read_json(nested_arch) == nested_before, (
        "Nested arch was mutated despite ambiguous filename"
    )


# ---------------------------------------------------------------------------
# AC #5: checkup --validate-arch-includes stays green with bundled examples
# ---------------------------------------------------------------------------


def test_ac5_checkup_validate_stays_green_with_examples(tmp_path: Path) -> None:
    """list_validate_arch_include_warnings(strict=False) must skip bundled samples,
    so a project that's clean in app code stays warning-free even when example
    arch files contain (intentional) mismatches."""
    (tmp_path / ".git").mkdir()
    # Root project — clean (no architecture.json -> no warnings).
    (tmp_path / "prompts").mkdir()

    # Bundled-sample arch with deliberate drift (declares a dep, prompt missing).
    ex_dir = tmp_path / "examples" / "arch"
    ex_prompts = ex_dir / "prompts"
    ex_prompts.mkdir(parents=True)
    (ex_prompts / "order_api_Python.prompt").write_text(
        "%\n<include>order_models_python.prompt</include>\n", encoding="utf-8"
    )
    _write_json(
        ex_dir / "architecture.json",
        [
            {
                "filename": "order_api_Python.prompt",
                "dependencies": ["order_models_Python.prompt"],
            },
        ],
    )

    warnings = list_validate_arch_include_warnings(tmp_path, strict=False)
    assert not warnings, (
        f"Bundled-sample warnings leaked into non-strict run: {warnings}"
    )


# ---------------------------------------------------------------------------
# AC #6: real nested non-sample arch is still discovered
# ---------------------------------------------------------------------------


def test_ac6_nested_non_sample_arch_still_discovered(tmp_path: Path) -> None:
    """services/api/architecture.json (and frontend/architecture.json) must still
    be discovered after the bundled-sample skip is applied."""
    (tmp_path / ".git").mkdir()
    _write_json(
        tmp_path / "architecture.json",
        [{"filename": "root_mod_python.prompt", "dependencies": []}],
    )
    _write_json(
        tmp_path / "services" / "api" / "architecture.json",
        [{"filename": "api_python.prompt", "dependencies": []}],
    )
    _write_json(
        tmp_path / "frontend" / "architecture.json",
        [{"filename": "Page_TypeScriptReact.prompt", "dependencies": []}],
    )

    arch_files = find_architecture_for_project(tmp_path)
    rel = sorted(str(p.relative_to(tmp_path).as_posix()) for p in arch_files)
    assert rel == [
        "architecture.json",
        "frontend/architecture.json",
        "services/api/architecture.json",
    ], f"Real nested arch dropped from discovery: {rel}"


# ---------------------------------------------------------------------------
# Bonus: opt-in strict discovery (parity with validator) still sees samples
# ---------------------------------------------------------------------------


def test_strict_discovery_returns_bundled_samples(tmp_path: Path) -> None:
    """When skip_bundled_sample_arch=False is opted in, bundled-sample trees are
    returned (preserves the existing strict validator behavior)."""
    (tmp_path / ".git").mkdir()
    _write_json(
        tmp_path / "architecture.json",
        [{"filename": "root_mod_python.prompt", "dependencies": []}],
    )
    _write_json(
        tmp_path / "examples" / "arch" / "architecture.json",
        [{"filename": "order_api_Python.prompt", "dependencies": []}],
    )

    arch_files = find_architecture_for_project(
        tmp_path, skip_bundled_sample_arch=False
    )
    rel = sorted(str(p.relative_to(tmp_path).as_posix()) for p in arch_files)
    assert rel == [
        "architecture.json",
        "examples/arch/architecture.json",
    ]


# ---------------------------------------------------------------------------
# AC #7 (round 2): dict-wrapper preservation on correction
# ---------------------------------------------------------------------------


def test_dict_wrapper_arch_preserves_prd_files_on_correction(tmp_path: Path) -> None:
    """When the owning architecture.json is in object/dict format
    (``{prd_files, modules}``), a correction must preserve the dict
    wrapper AND the prd_files list. The old write path wrote a bare list
    and silently dropped prd_files (issue #1060 Layer 2 follow-up)."""
    (tmp_path / ".git").mkdir()
    root_arch = tmp_path / "architecture.json"
    nested_arch = tmp_path / "services" / "api" / "architecture.json"

    _write_json(
        root_arch,
        [{"filename": "root_mod_python.prompt", "dependencies": []}],
    )
    # Owning file is dict-shaped with real prd_files. The reproducer must
    # also write the wrapper through json.dumps (not the test helper) so we
    # can assert the wrapper shape survives.
    nested_arch.parent.mkdir(parents=True, exist_ok=True)
    nested_arch.write_text(
        json.dumps(
            {
                "prd_files": ["docs/prd.md", "docs/spec.md"],
                "modules": [
                    {
                        "filename": "api_python.prompt",
                        "dependencies": ["models_python.prompt"],
                    },
                    {"filename": "models_python.prompt", "dependencies": []},
                ],
            },
            indent=2,
        ),
        encoding="utf-8",
    )

    corrections = [
        {
            "filename": "api_python.prompt",
            "dependencies": ["models_python.prompt", "auth_python.prompt"],
        }
    ]
    _apply_architecture_corrections(tmp_path, corrections, quiet=True)

    reloaded = json.loads(nested_arch.read_text(encoding="utf-8"))
    assert isinstance(reloaded, dict), (
        "Owning dict-shaped architecture.json must remain a dict on write-back; "
        "got a bare list — the {prd_files, modules} wrapper was dropped."
    )
    assert reloaded.get("prd_files") == ["docs/prd.md", "docs/spec.md"], (
        f"prd_files must be preserved on correction; got {reloaded.get('prd_files')!r}"
    )
    modules_by_fn = {m["filename"]: m for m in reloaded["modules"]}
    assert modules_by_fn["api_python.prompt"]["dependencies"] == [
        "models_python.prompt",
        "auth_python.prompt",
    ]
