import json
from pathlib import Path
from typing import List

import pytest
from pydantic import ValidationError

from pdd import DEFAULT_STRENGTH, DEFAULT_TIME
from pdd.incremental_prd_architecture import (
    ArchitecturePatch,
    DependencyUpdate,
    ModuleModification,
    ModuleRemoval,
    ModuleToAdd,
    apply_architecture_patch,
    run_incremental_prd_propagation,
)


def _module(filename: str, *, deps=None, description=None):
    return {
        "filename": filename,
        "reason": f"{filename} reason",
        "description": description or f"{filename} description",
        "dependencies": deps or [],
        "priority": 1,
        "filepath": f"src/{filename.replace('.prompt', '.py')}",
        "tags": ["module", "python"],
        "interface": {"type": "module"},
    }


def test_apply_architecture_patch_preserves_unrelated_entries_and_prd_files():
    raw = {
        "prd_files": ["docs/prd.md"],
        "modules": [
            _module("database_python.prompt"),
            _module("api_router_python.prompt", deps=["database_python.prompt"]),
            _module("user_service_python.prompt", deps=["database_python.prompt"]),
        ],
    }
    patch = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_logger_python.prompt",
                reason="Audit event emission for mutations",
                dependencies=["database_python.prompt"],
                interface={"type": "module", "module": {"functions": []}},
                requirements=["Emit audit events for API mutations."],
            )
        ],
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"description": "API routing with audit logging for mutations."},
                justification="PRD added audit logging for mutation endpoints.",
            )
        ],
        dependency_updates=[
            DependencyUpdate(
                source="api_router_python.prompt",
                add=["audit_logger_python.prompt"],
                justification="API router must call the audit logger.",
            )
        ],
    )

    result = apply_architecture_patch(raw, patch)

    assert result.raw_architecture["prd_files"] == ["docs/prd.md"]
    modules = {entry["filename"]: entry for entry in result.modules}
    assert modules["database_python.prompt"] == raw["modules"][0]
    assert modules["api_router_python.prompt"]["description"] == "API routing with audit logging for mutations."
    assert modules["api_router_python.prompt"]["dependencies"] == [
        "database_python.prompt",
        "audit_logger_python.prompt",
    ]
    assert modules["audit_logger_python.prompt"]["reason"] == "Audit event emission for mutations"
    assert "architecture.json.before" in result.architecture_diff


def test_apply_architecture_patch_rejects_unknown_dependency_target():
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        dependency_updates=[
            DependencyUpdate(
                source="api_router_python.prompt",
                add=["missing_python.prompt"],
                justification="Bad dependency.",
            )
        ]
    )

    with pytest.raises(ValueError, match="depends on unknown module"):
        apply_architecture_patch(raw, patch)


def test_apply_architecture_patch_rejects_new_cycles():
    raw = [
        _module("a_python.prompt"),
        _module("b_python.prompt", deps=["a_python.prompt"]),
    ]
    patch = ArchitecturePatch(
        dependency_updates=[
            DependencyUpdate(
                source="a_python.prompt",
                add=["b_python.prompt"],
                justification="Would create a cycle.",
            )
        ]
    )

    with pytest.raises(ValueError, match="circular dependencies"):
        apply_architecture_patch(raw, patch)


def test_apply_architecture_patch_rejects_removal_that_leaves_dependents():
    raw = [
        _module("audit_logger_python.prompt"),
        _module("api_router_python.prompt", deps=["audit_logger_python.prompt"]),
    ]
    patch = ArchitecturePatch(
        modules_to_remove=[
            {
                "filename": "audit_logger_python.prompt",
                "justification": "PRD explicitly removed audit logging.",
            }
        ]
    )

    with pytest.raises(ValueError, match="still depends on removed module"):
        apply_architecture_patch(raw, patch)


def test_run_incremental_prd_dry_run_does_not_write_files(tmp_path, monkeypatch):
    docs = tmp_path / "docs"
    docs.mkdir()
    prd = docs / "prd.md"
    prd.write_text("Add audit logging.", encoding="utf-8")

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "api_router_python.prompt").write_text(
        "<pdd-reason>Old</pdd-reason>\n\n## Requirements\n\n- Route requests.\n",
        encoding="utf-8",
    )
    arch_path = tmp_path / "architecture.json"
    original_arch = {
        "prd_files": ["docs/prd.md"],
        "modules": [_module("api_router_python.prompt")],
    }
    arch_path.write_text(json.dumps(original_arch, indent=2), encoding="utf-8")

    patch = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_logger_python.prompt",
                reason="Audit event emission",
                interface={"type": "module"},
                requirements=["Emit audit events."],
            )
        ],
        dependency_updates=[
            DependencyUpdate(
                source="api_router_python.prompt",
                add=["audit_logger_python.prompt"],
                justification="API router calls audit logger.",
            )
        ],
    )

    monkeypatch.setattr(
        "pdd.incremental_prd_architecture._ask_llm_for_patch",
        lambda **_: (patch, 0.25, "mock-model"),
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture.detect_change",
        lambda *_, **__: ([], 0.0, "mock-model"),
    )

    success, message, cost, model, changed_files = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        dry_run=True,
        quiet=True,
    )

    assert success is True
    assert "Dry run" in message
    assert cost == 0.25
    assert model == "mock-model"
    assert "architecture.json" in changed_files
    assert not (prompts / "audit_logger_python.prompt").exists()
    assert json.loads(arch_path.read_text(encoding="utf-8")) == original_arch
    assert not (tmp_path / ".pdd" / "meta" / "prd_hashes.json").exists()


def test_run_incremental_prd_updates_prompt_requirements_and_snapshot(tmp_path, monkeypatch):
    docs = tmp_path / "docs"
    docs.mkdir()
    prd = docs / "prd.md"
    prd.write_text("Add audit logging.", encoding="utf-8")

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    prompt = prompts / "api_router_python.prompt"
    prompt.write_text(
        "<pdd-reason>Old</pdd-reason>\n\n## Requirements\n\n- Route requests.\n",
        encoding="utf-8",
    )
    src = tmp_path / "src"
    src.mkdir()
    (src / "api_router_python.py").write_text("def route(): pass\n", encoding="utf-8")

    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps(
            {
                "prd_files": ["docs/prd.md"],
                "modules": [
                    {
                        **_module("api_router_python.prompt"),
                        "filepath": "src/api_router_python.py",
                    }
                ],
            },
            indent=2,
        ),
        encoding="utf-8",
    )

    patch = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"description": "API routing with audit logging."},
                justification="PRD added audit logging.",
            )
        ]
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture._ask_llm_for_patch",
        lambda **_: (patch, 0.25, "patch-model"),
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture.detect_change",
        lambda *_, **__: (
            [
                {
                    "prompt_name": "api_router_python.prompt",
                    "change_instructions": "Add audit logging to Requirements.",
                }
            ],
            0.10,
            "detect-model",
        ),
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture.change",
        lambda **_: (
            "## Requirements\n\n- Route requests.\n- Emit audit events for mutations.\n",
            0.20,
            "change-model",
        ),
    )

    success, message, cost, model, changed_files = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        quiet=True,
    )

    assert success is True
    assert "Applied" in message
    assert cost == pytest.approx(0.55)
    assert model == "change-model"
    assert "prompts/api_router_python.prompt" in changed_files
    prompt_text = prompt.read_text(encoding="utf-8")
    assert "Emit audit events" in prompt_text
    assert prompt_text.startswith("<pdd-reason>")
    assert "<pdd-interface>" in prompt_text

    arch = json.loads(arch_path.read_text(encoding="utf-8"))
    assert arch["modules"][0]["description"] == "API routing with audit logging."

    snapshot = json.loads((tmp_path / ".pdd" / "meta" / "prd_hashes.json").read_text(encoding="utf-8"))
    entry = snapshot["sources"]["docs/prd.md"]
    assert entry["hash"]
    assert entry["source_type"] == "local_file"
    assert "content" not in entry
    assert "Add audit logging." not in json.dumps(snapshot)
    cache_path = tmp_path / ".pdd" / "cache" / "prd_snapshots" / entry["cache_key"]
    assert cache_path.read_text(encoding="utf-8") == "Add audit logging."
    assert (tmp_path / ".pdd" / "cache" / ".gitignore").read_text(
        encoding="utf-8"
    ) == "*\n!.gitignore\n"


def test_prd_snapshot_cache_supplies_previous_content_without_tracked_raw_text(
    tmp_path,
    monkeypatch,
):
    docs = tmp_path / "docs"
    docs.mkdir()
    prd = docs / "prd.md"
    prd.write_text("Add audit logging.", encoding="utf-8")

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps(
            {
                "prd_files": ["docs/prd.md"],
                "modules": [_module("api_router_python.prompt")],
            },
            indent=2,
        ),
        encoding="utf-8",
    )

    patch = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"description": "API routing with audit logging."},
                justification="PRD added audit logging.",
            )
        ]
    )
    seen_diffs: List[str] = []

    def fake_ask(**kwargs):
        seen_diffs.append(kwargs["prd_diff"])
        return patch, 0.0, "patch-model"

    monkeypatch.setattr(
        "pdd.incremental_prd_architecture._ask_llm_for_patch",
        fake_ask,
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture.detect_change",
        lambda *_, **__: ([], 0.0, "m"),
    )

    success, message, _, _, _ = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        project_root=tmp_path,
        quiet=True,
    )
    assert success is True, message

    metadata = json.loads(
        (tmp_path / ".pdd" / "meta" / "prd_hashes.json").read_text(
            encoding="utf-8"
        )
    )
    assert "content" not in json.dumps(metadata)
    assert "Add audit logging." not in json.dumps(metadata)

    prd.write_text("Add audit logging.\nAdd metrics.", encoding="utf-8")
    success, message, _, _, _ = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        project_root=tmp_path,
        quiet=True,
    )
    assert success is True, message
    assert "--- docs/prd.md.previous" in seen_diffs[-1]
    assert "-Add audit logging." in seen_diffs[-1]
    assert "+Add metrics." in seen_diffs[-1]


def test_prd_snapshot_save_sanitizes_legacy_raw_content(tmp_path):
    from pdd.incremental_prd_architecture import _save_prd_snapshot

    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    (meta / "prd_hashes.json").write_text(
        json.dumps(
            {
                "version": 1,
                "sources": {
                    "docs/old.md": {
                        "hash": "old",
                        "content": "legacy secret PRD body",
                        "updated_at": "2026-01-01T00:00:00+00:00",
                    }
                },
            }
        ),
        encoding="utf-8",
    )

    _save_prd_snapshot(tmp_path, "docs/new.md", "new body")

    metadata_text = (meta / "prd_hashes.json").read_text(encoding="utf-8")
    assert "legacy secret PRD body" not in metadata_text
    assert "new body" not in metadata_text


def test_no_change_run_migrates_legacy_raw_snapshot_metadata(tmp_path, monkeypatch):
    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("same PRD body", encoding="utf-8")

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps(
            {
                "prd_files": ["docs/prd.md"],
                "modules": [_module("api_router_python.prompt")],
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    (meta / "prd_hashes.json").write_text(
        json.dumps(
            {
                "version": 1,
                "sources": {
                    "docs/prd.md": {
                        "hash": "legacy",
                        "content": "same PRD body",
                        "updated_at": "2026-01-01T00:00:00+00:00",
                    }
                },
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture._ask_llm_for_patch",
        lambda **_: pytest.fail("LLM should not be called for unchanged PRD"),
    )

    success, message, cost, model, changed = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        project_root=tmp_path,
        quiet=True,
    )

    assert success is True
    assert "No PRD changes detected" in message
    assert "hash-only" in message
    assert cost == 0.0
    assert model == ""
    assert changed == [".pdd/meta/prd_hashes.json"]
    metadata_text = (meta / "prd_hashes.json").read_text(encoding="utf-8")
    assert "same PRD body" not in metadata_text


def test_run_incremental_prd_retries_after_patch_validation_error(tmp_path, monkeypatch):
    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add audit logging.", encoding="utf-8")

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps({"modules": [_module("api_router_python.prompt")]}, indent=2),
        encoding="utf-8",
    )

    bad_patch = ArchitecturePatch(
        dependency_updates=[
            DependencyUpdate(
                source="api_router_python.prompt",
                add=["missing_python.prompt"],
                justification="Bad first attempt.",
            )
        ]
    )
    good_patch = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_logger_python.prompt",
                reason="Audit event emission",
                dependencies=[],
                interface={"type": "module"},
            )
        ],
        dependency_updates=[
            DependencyUpdate(
                source="api_router_python.prompt",
                add=["audit_logger_python.prompt"],
                justification="API router calls audit logger.",
            )
        ],
    )
    seen_validation_errors = []
    patches = iter([bad_patch, good_patch])

    def fake_ask(**kwargs):
        seen_validation_errors.append(list(kwargs.get("validation_errors", [])))
        return next(patches), 0.10, "mock-model"

    monkeypatch.setattr("pdd.incremental_prd_architecture._ask_llm_for_patch", fake_ask)
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture.detect_change",
        lambda *_, **__: ([], 0.0, "mock-model"),
    )

    success, message, cost, model, changed_files = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        quiet=True,
    )

    assert success is True
    assert "Applied" in message
    assert cost == pytest.approx(0.20)
    assert model == "mock-model"
    assert "architecture.json" in changed_files
    assert seen_validation_errors[0] == []
    assert "depends on unknown module" in seen_validation_errors[1][0]


def test_ask_llm_for_patch_formats_retry_validation_errors(monkeypatch):
    import pdd.incremental_prd_architecture as ipa

    captured = {}

    monkeypatch.setattr(
        ipa,
        "load_prompt_template",
        lambda name: (
            "Source: {PRD_SOURCE}\n"
            "Diff: {PRD_DIFF}\n"
            "Architecture: {CURRENT_ARCHITECTURE}\n"
            "Errors: {VALIDATION_ERRORS}\n"
        ),
    )

    def fake_llm_invoke(**kwargs):
        captured["formatted_prompt"] = kwargs["prompt"].format(**kwargs["input_json"])
        return {"result": ArchitecturePatch(), "cost": 0.0, "model_name": "mock-model"}

    monkeypatch.setattr(ipa, "llm_invoke", fake_llm_invoke)

    patch, cost, model = ipa._ask_llm_for_patch(
        prd_source="docs/prd.md",
        prd_diff="Add audit logging.",
        architecture=[],
        strength=DEFAULT_STRENGTH,
        temperature=0.0,
        time=DEFAULT_TIME,
        verbose=False,
        validation_errors=["api_python.prompt depends on missing_python.prompt"],
    )

    assert isinstance(patch, ArchitecturePatch)
    assert cost == 0.0
    assert model == "mock-model"
    assert "- api_python.prompt depends on missing_python.prompt" in captured["formatted_prompt"]
    assert "{VALIDATION_ERRORS}" not in captured["formatted_prompt"]


def test_run_incremental_prd_fails_after_repeated_invalid_patches(tmp_path, monkeypatch):
    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add audit logging.", encoding="utf-8")

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    arch_path = tmp_path / "architecture.json"
    original_arch = {"modules": [_module("api_router_python.prompt")]}
    arch_path.write_text(json.dumps(original_arch, indent=2), encoding="utf-8")

    bad_patch = ArchitecturePatch(
        dependency_updates=[
            DependencyUpdate(
                source="api_router_python.prompt",
                add=["missing_python.prompt"],
                justification="Bad dependency.",
            )
        ]
    )

    monkeypatch.setattr(
        "pdd.incremental_prd_architecture._ask_llm_for_patch",
        lambda **_: (bad_patch, 0.10, "mock-model"),
    )

    success, message, cost, model, changed_files = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        quiet=True,
        max_patch_attempts=2,
    )

    assert success is False
    assert "failed validation after 2 attempt" in message
    assert cost == pytest.approx(0.20)
    assert model == "mock-model"
    assert changed_files == []
    assert json.loads(arch_path.read_text(encoding="utf-8")) == original_arch
    assert not (tmp_path / ".pdd" / "meta" / "prd_hashes.json").exists()


# --- F1: filepath path-traversal validation ----------------------------------


@pytest.mark.parametrize(
    "bad_filename",
    [
        "audit logger_python.prompt",
        "audit`logger_python.prompt",
        "audit\nlogger_python.prompt",
        "-audit_logger_python.prompt",
        ".audit_logger_python.prompt",
    ],
)
def test_apply_architecture_patch_rejects_unsafe_prompt_filename(bad_filename):
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename=bad_filename,
                reason="r",
                interface={"type": "module"},
            )
        ]
    )
    with pytest.raises(ValueError, match="Invalid architecture prompt filename"):
        apply_architecture_patch(raw, patch)


def test_apply_architecture_patch_accepts_safe_nested_prompt_filename():
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="commands/audit_logger_python.prompt",
                reason="r",
                interface={"type": "module"},
            )
        ]
    )
    result = apply_architecture_patch(raw, patch)
    filenames = {module["filename"] for module in result.modules}
    assert "commands/audit_logger_python.prompt" in filenames


@pytest.mark.parametrize(
    "bad_filepath",
    [
        "../../etc/passwd",
        "/etc/passwd",
        "..\\windows\\system32",
        "src\\..\\..\\outside.py",
        "src/../../outside.py",
        ".env",
        "src/.env",
        "src/private.pem",
        "config/secrets.json",
        ".github/workflows/ci.yml",
        "src/audit logger.py",
        "src/audit`logger.py",
        "src/audit\nlogger.py",
        "-src/audit_logger.py",
        "src/-audit_logger.py",
    ],
)
def test_apply_architecture_patch_rejects_path_traversal_in_module_add_filepath(bad_filepath):
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_logger_python.prompt",
                reason="r",
                interface={"type": "module"},
                filepath=bad_filepath,
            )
        ]
    )
    with pytest.raises(ValueError, match="Invalid module filepath"):
        apply_architecture_patch(raw, patch)


@pytest.mark.parametrize(
    "bad_filepath",
    [
        "../../etc/passwd",
        "/etc/passwd",
        "..\\windows\\system32",
        ".env",
        "src/.env",
        "src/private.pem",
        "config/secrets.json",
        ".github/workflows/ci.yml",
        "src/audit logger.py",
        "src/audit`logger.py",
        "src/audit\nlogger.py",
        "-src/audit_logger.py",
        "src/-audit_logger.py",
    ],
)
def test_apply_architecture_patch_rejects_path_traversal_in_modules_to_modify_filepath(bad_filepath):
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"filepath": bad_filepath},
                justification="bad path",
            )
        ]
    )
    with pytest.raises(ValueError, match="Invalid module filepath"):
        apply_architecture_patch(raw, patch)


def test_apply_architecture_patch_accepts_safe_relative_filepath():
    """Sanity check: a normal relative filepath must still pass validation."""
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_logger_python.prompt",
                reason="audit",
                interface={"type": "module"},
                filepath="src/audit_logger_python.py",
            )
        ]
    )
    result = apply_architecture_patch(raw, patch)
    new_entry = next(m for m in result.modules if m["filename"] == "audit_logger_python.prompt")
    assert new_entry["filepath"] == "src/audit_logger_python.py"


def test_read_code_for_entry_refuses_traversal_filepath(tmp_path):
    """Defense-in-depth: even if filepath got through, _read_code_for_entry must refuse."""
    from pdd.incremental_prd_architecture import _read_code_for_entry

    secret = tmp_path.parent / "outside-secret.txt"
    secret.write_text("SECRET", encoding="utf-8")
    project_root = tmp_path / "project"
    project_root.mkdir()

    entry = {"filepath": f"../{secret.name}"}
    result = _read_code_for_entry(entry, project_root)

    assert result == "No existing code file is available for this prompt yet."
    assert "SECRET" not in result


@pytest.mark.parametrize(
    "filepath",
    [".env", "src/.env", "src/private.pem", "config/secrets.json"],
)
def test_read_code_for_entry_refuses_hidden_or_secret_filepath(tmp_path, filepath):
    """LLM-controlled filepath values must not leak local secrets into change()."""
    from pdd.incremental_prd_architecture import _read_code_for_entry

    project_root = tmp_path / "project"
    secret_path = project_root / filepath
    secret_path.parent.mkdir(parents=True, exist_ok=True)
    secret_path.write_text("SECRET_TOKEN=abc123", encoding="utf-8")

    result = _read_code_for_entry({"filepath": filepath}, project_root)

    assert result == "No existing code file is available for this prompt yet."
    assert "SECRET_TOKEN" not in result


# --- F2: writes are transactional --------------------------------------------


def test_run_incremental_prd_rolls_back_partial_commit_phase_writes(tmp_path, monkeypatch):
    """If a prompt write fails AFTER the architecture write, the architecture
    must be restored to its pre-run state, the new module's prompt file must
    not be left on disk, and the PRD snapshot must NOT advance.
    """
    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add audit logging.", encoding="utf-8")

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    api_router_prompt = prompts / "api_router_python.prompt"
    api_router_prompt.write_text(
        "<pdd-reason>old</pdd-reason>\n<pdd-interface>{}</pdd-interface>\n\n"
        "## Requirements\n\n- Route requests.\n",
        encoding="utf-8",
    )

    arch_path = tmp_path / "architecture.json"
    original_arch = {
        "prd_files": ["docs/prd.md"],
        "modules": [_module("api_router_python.prompt")],
    }
    arch_path.write_text(json.dumps(original_arch, indent=2), encoding="utf-8")

    pre_arch_bytes = arch_path.read_bytes()
    pre_router_bytes = api_router_prompt.read_bytes()

    patch_obj = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_logger_python.prompt",
                reason="Audit",
                interface={"type": "module"},
                requirements=["Emit audit events."],
            )
        ],
        dependency_updates=[
            DependencyUpdate(
                source="api_router_python.prompt",
                add=["audit_logger_python.prompt"],
                justification="API router calls audit logger.",
            )
        ],
    )

    monkeypatch.setattr(
        "pdd.incremental_prd_architecture._ask_llm_for_patch",
        lambda **_: (patch_obj, 0.05, "mock"),
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture.detect_change",
        lambda *_, **__: ([], 0.0, "mock"),
    )

    # Simulate disk failure on the FIRST .prompt write only (after arch is committed)
    import pdd.incremental_prd_architecture as ipa

    real_atomic_write_text = ipa._atomic_write_text
    fail_for_prompt = {"first": True}

    def flaky_write(path, content):
        if str(path).endswith(".prompt") and fail_for_prompt["first"]:
            fail_for_prompt["first"] = False
            raise OSError("disk full simulated")
        return real_atomic_write_text(path, content)

    monkeypatch.setattr(ipa, "_atomic_write_text", flaky_write)

    success, message, cost, model, changed = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        quiet=True,
    )

    assert success is False
    assert "rolled back" in message
    assert changed == []
    # architecture restored
    assert arch_path.read_bytes() == pre_arch_bytes
    # api_router prompt content unchanged
    assert api_router_prompt.read_bytes() == pre_router_bytes
    # New prompt file not left on disk
    assert not (prompts / "audit_logger_python.prompt").exists()
    # PRD snapshot did not advance
    assert not (tmp_path / ".pdd" / "meta" / "prd_hashes.json").exists()


def test_run_incremental_prd_no_partial_state_on_change_failure(tmp_path, monkeypatch):
    """If detect_change/change raises during the compute phase, NO file on disk
    is modified — no architecture write, no prompt write, no PRD snapshot.
    """
    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add audit logging.", encoding="utf-8")

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    prompt = prompts / "api_router_python.prompt"
    prompt.write_text(
        "<pdd-reason>old</pdd-reason>\n\n## Requirements\n\n- Route requests.\n",
        encoding="utf-8",
    )

    arch_path = tmp_path / "architecture.json"
    original_arch = {
        "prd_files": ["docs/prd.md"],
        "modules": [_module("api_router_python.prompt")],
    }
    arch_path.write_text(json.dumps(original_arch, indent=2), encoding="utf-8")

    patch = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"description": "Modified routing description."},
                justification="PRD changed.",
            )
        ]
    )

    pre_arch_md5 = arch_path.read_bytes()
    pre_prompt_md5 = prompt.read_bytes()

    monkeypatch.setattr(
        "pdd.incremental_prd_architecture._ask_llm_for_patch",
        lambda **_: (patch, 0.10, "mock"),
    )

    def boom(*args, **kwargs):
        raise RuntimeError("forced detect_change failure")

    monkeypatch.setattr("pdd.incremental_prd_architecture.detect_change", boom)

    success, message, cost, model, changed = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        quiet=True,
    )

    assert success is False
    assert "before any disk write" in message
    assert changed == []
    # Files unchanged
    assert arch_path.read_bytes() == pre_arch_md5
    assert prompt.read_bytes() == pre_prompt_md5
    # No PRD snapshot
    assert not (tmp_path / ".pdd" / "meta" / "prd_hashes.json").exists()


# --- F5: dry-run shows full prompt content changes ---------------------------


def test_run_incremental_prd_dry_run_prints_prompt_diffs(tmp_path, monkeypatch, capsys):
    """Dry-run must print actual content/diff for each affected prompt, not just
    file paths.
    """
    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add audit logging.", encoding="utf-8")

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    prompt = prompts / "api_router_python.prompt"
    prompt.write_text(
        "<pdd-reason>old</pdd-reason>\n<pdd-interface>{}</pdd-interface>\n\n"
        "## Requirements\n\n- Route requests.\n",
        encoding="utf-8",
    )

    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps(
            {
                "prd_files": ["docs/prd.md"],
                "modules": [_module("api_router_python.prompt")],
            },
            indent=2,
        ),
        encoding="utf-8",
    )

    patch = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_logger_python.prompt",
                reason="audit",
                interface={"type": "module"},
                requirements=["Emit audit events."],
            )
        ],
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"description": "API routing with audit logging."},
                justification="PRD added audit logging.",
            )
        ],
    )

    monkeypatch.setattr(
        "pdd.incremental_prd_architecture._ask_llm_for_patch",
        lambda **_: (patch, 0.10, "mock"),
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture.detect_change",
        lambda *_, **__: (
            [{"prompt_name": "api_router_python.prompt",
              "change_instructions": "Add audit logging."}],
            0.05,
            "detect",
        ),
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture.change",
        lambda **_: (
            "<pdd-reason>old</pdd-reason>\n<pdd-interface>{}</pdd-interface>\n\n"
            "## Requirements\n\n- Route requests.\n- Emit audit events for mutations.\n",
            0.05,
            "change",
        ),
    )

    success, _, _, _, _ = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        dry_run=True,
        quiet=False,
    )
    assert success is True

    out = capsys.readouterr().out

    # Architecture diff is shown
    assert "architecture.json" in out
    # New prompt full content preview is shown
    assert "audit_logger_python.prompt" in out
    assert "NEW FILE" in out
    assert "Emit audit events" in out
    # Modified prompt unified diff is shown with the new requirement bullet
    assert "Requirements update" in out
    assert "Emit audit events for mutations" in out


# --- F4: new prompt generation includes deps + interface ---------------------


def test_new_prompt_content_includes_dependency_includes_and_interface():
    """_new_prompt_content must add <include> tags for each dependency and an
    Interface Specification block when interface metadata is supplied."""
    from pdd.incremental_prd_architecture import _new_prompt_content

    module = ModuleToAdd(
        filename="audit_logger_python.prompt",
        reason="Audit log",
        description="Persists API mutation events.",
        dependencies=["database_python.prompt", "config_python.prompt"],
        interface={
            "type": "module",
            "module": {
                "functions": [
                    {
                        "name": "log_audit_event",
                        "signature": "(user_id: str, action: str)",
                        "returns": "bool",
                    }
                ],
                "classes": [{"name": "AuditEvent"}],
            },
        },
        requirements=["Emit audit events for API mutations.",
                      "Return True on success."],
    )
    body = _new_prompt_content(module)

    # PDD metadata tags
    assert "<pdd-reason>" in body
    assert "<pdd-dependency>database_python.prompt</pdd-dependency>" in body
    # Runtime <include> tags for each declared dependency
    # (path relative to project root so preprocess resolves them)
    assert "<include>prompts/database_python.prompt</include>" in body
    assert "<include>prompts/config_python.prompt</include>" in body
    # Role / Requirements still present
    assert "## Role" in body
    assert "## Requirements" in body
    assert "Emit audit events for API mutations." in body
    # Interface Specification rendered from interface metadata
    assert "## Interface Specification" in body
    assert "log_audit_event(user_id: str, action: str)" in body
    assert "AuditEvent" in body
    # Dependencies section names each dep
    assert "## Dependencies" in body
    assert "`database_python.prompt`" in body
    assert "`config_python.prompt`" in body


def test_new_prompt_content_handles_empty_dependencies_and_interface():
    """When no deps or interface, no extra empty sections are written."""
    from pdd.incremental_prd_architecture import _new_prompt_content

    module = ModuleToAdd(
        filename="solo_python.prompt",
        reason="Standalone helper",
        interface={},
    )
    body = _new_prompt_content(module)

    assert "<include>" not in body  # no deps -> no include lines
    assert "## Dependencies" not in body
    assert "## Interface Specification" not in body
    assert "## Role" in body
    assert "## Requirements" in body


# --- F11: _read_github_issue_prd filters bot status comments ---------------


def test_read_github_issue_prd_skips_pdd_status_comments(monkeypatch):
    """Direct API call must not feed pdd's own incremental status output back
    in as PRD content on the next run."""
    import subprocess as _sub
    from pdd.incremental_prd_architecture import (
        INCREMENTAL_STATUS_MARKER,
        _read_github_issue_prd,
    )

    payload = {
        "title": "Add audit logging",
        "body": "All API mutations must emit audit events.",
        "comments": [
            {"body": "Looks good — please add user_id."},
            {
                "body": (
                    f"{INCREMENTAL_STATUS_MARKER}\n"
                    "pdd incremental architecture update successful.\n"
                    "Result: Applied incremental PRD propagation: 1 affected"
                )
            },
            {"body": "Approved."},
        ],
    }

    class FakeProc:
        returncode = 0
        stdout = json.dumps(payload)
        stderr = ""

    monkeypatch.setattr(_sub, "run", lambda *a, **k: FakeProc())

    text = _read_github_issue_prd("https://github.com/o/r/issues/1")

    assert "Add audit logging" in text  # title
    assert "All API mutations must emit audit events." in text  # body
    assert "Looks good" in text  # human comment
    assert "Approved" in text  # human comment
    assert INCREMENTAL_STATUS_MARKER not in text
    assert "pdd incremental architecture update" not in text


# --- F12: changed_files contains project-root-relative paths -----------------


def test_changed_files_are_relative_to_project_root(tmp_path, monkeypatch):
    """The user-facing changed_files list (also posted to GitHub status comments)
    must contain project-root-relative paths, not absolute filesystem paths
    that leak local username / temp dirs.
    """
    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add audit logging.", encoding="utf-8")

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    prompt = prompts / "api_router_python.prompt"
    prompt.write_text(
        "<pdd-reason>routing</pdd-reason>\n<pdd-interface>{}</pdd-interface>\n\n"
        "## Requirements\n\n- Route requests.\n",
        encoding="utf-8",
    )

    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps(
            {
                "prd_files": ["docs/prd.md"],
                "modules": [_module("api_router_python.prompt")],
            },
            indent=2,
        ),
        encoding="utf-8",
    )

    patch_obj = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"description": "Routing with audit logging."},
                justification="PRD added audit logging.",
            )
        ],
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture._ask_llm_for_patch",
        lambda **_: (patch_obj, 0.05, "mock"),
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture.detect_change",
        lambda *_, **__: ([], 0.0, "mock"),
    )

    success, _, _, _, changed_files = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        project_root=tmp_path,
        quiet=True,
    )
    assert success is True

    # Every entry must be a relative path with no absolute / temp-dir leakage
    assert "architecture.json" in changed_files
    for entry in changed_files:
        assert not Path(entry).is_absolute(), f"absolute path leaked: {entry}"
        assert str(tmp_path) not in entry, f"abs tmp_path leaked: {entry}"
        assert not entry.startswith("/"), f"leading slash in: {entry}"


# --- F10: full-phase commit lock prevents concurrent-run interleaving --------


# --- F16: per-field type validation in modules_to_modify.changes -----------


def test_apply_architecture_patch_rejects_non_string_reason():
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"reason": ["not", "a", "string"]},
                justification="bad type",
            )
        ]
    )
    with pytest.raises(ValueError, match=r"change field 'reason'.*must be a string"):
        apply_architecture_patch(raw, patch)


def test_apply_architecture_patch_rejects_non_dict_interface():
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"interface": "not-a-dict"},
                justification="bad type",
            )
        ]
    )
    with pytest.raises(ValueError, match=r"change field 'interface'.*must be an object"):
        apply_architecture_patch(raw, patch)


def test_apply_architecture_patch_rejects_non_list_tags():
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"tags": "not-a-list"},
                justification="bad type",
            )
        ]
    )
    with pytest.raises(ValueError, match=r"change field 'tags'.*must be a list"):
        apply_architecture_patch(raw, patch)


def test_apply_architecture_patch_rejects_non_string_tag_element():
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"tags": ["good", 123]},  # not all strings
                justification="bad element",
            )
        ]
    )
    with pytest.raises(ValueError, match=r"change field 'tags'.*list of strings"):
        apply_architecture_patch(raw, patch)


def test_apply_architecture_patch_rejects_non_int_priority():
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"priority": "high"},
                justification="bad type",
            )
        ]
    )
    with pytest.raises(ValueError, match=r"change field 'priority'.*must be an int"):
        apply_architecture_patch(raw, patch)


def test_module_to_add_rejects_bool_priority():
    with pytest.raises(ValidationError):
        ArchitecturePatch(
            modules_to_add=[
                {
                    "filename": "audit_logger_python.prompt",
                    "reason": "audit",
                    "priority": True,
                }
            ]
        )


def test_added_module_priorities_follow_dependency_order():
    raw = [_module("base_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="api_python.prompt",
                reason="api",
                dependencies=["db_python.prompt"],
            ),
            ModuleToAdd(
                filename="db_python.prompt",
                reason="db",
            ),
        ]
    )

    result = apply_architecture_patch(raw, patch)
    modules = {entry["filename"]: entry for entry in result.modules}

    assert modules["db_python.prompt"]["priority"] < modules["api_python.prompt"]["priority"]


def test_existing_module_priority_bumped_when_it_depends_on_new_module():
    raw = [_module("api_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_python.prompt",
                reason="audit",
            ),
        ],
        dependency_updates=[
            DependencyUpdate(
                source="api_python.prompt",
                add=["audit_python.prompt"],
                justification="api must emit audit events",
            )
        ],
    )

    result = apply_architecture_patch(raw, patch)
    modules = {entry["filename"]: entry for entry in result.modules}

    assert modules["audit_python.prompt"]["priority"] < modules["api_python.prompt"]["priority"]


def test_apply_architecture_patch_rejects_bool_priority():
    """Python treats bool as a subtype of int — explicitly reject."""
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"priority": True},
                justification="bad type",
            )
        ]
    )
    with pytest.raises(ValueError, match=r"change field 'priority'.*must be an int"):
        apply_architecture_patch(raw, patch)


def test_apply_architecture_patch_accepts_well_typed_changes():
    """Sanity: well-typed values for every supported field still pass."""
    raw = [_module("api_router_python.prompt")]
    patch = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={
                    "reason": "new reason",
                    "description": "new description",
                    "interface": {"type": "module"},
                    "filepath": "src/api_router_python.py",
                    "tags": ["api", "python"],
                    "priority": 42,
                },
                justification="all good",
            )
        ]
    )
    result = apply_architecture_patch(raw, patch)
    after = next(m for m in result.modules if m["filename"] == "api_router_python.prompt")
    assert after["reason"] == "new reason"
    assert after["priority"] == 42
    assert after["tags"] == ["api", "python"]


def test_baseline_capture_is_atomic_with_parse(tmp_path, monkeypatch):
    """F14: defeat the TOCTOU between `_load_architecture` and a separate
    `read_bytes` baseline capture. If a concurrent run commits between those
    reads, we must NOT compute a patch off the old parsed content while the
    baseline reflects the new bytes — the under-lock guard would then pass
    and silently overwrite the other run's commit.

    We force the race by patching `_load_architecture_with_bytes` so that
    immediately after it returns, another writer changes architecture.json
    on disk. The under-lock guard must still detect the change.
    """
    import pdd.incremental_prd_architecture as ipa

    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add audit logging.", encoding="utf-8")
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    arch_path = tmp_path / "architecture.json"
    original_arch = {
        "prd_files": ["docs/prd.md"],
        "modules": [_module("api_router_python.prompt")],
    }
    arch_path.write_text(json.dumps(original_arch, indent=2), encoding="utf-8")

    other_arch = {
        "prd_files": ["docs/prd.md"],
        "modules": [
            _module("api_router_python.prompt"),
            _module("cache_python.prompt"),
        ],
    }
    other_arch_bytes = (json.dumps(other_arch, indent=2) + "\n").encode("utf-8")

    real_loader = ipa._load_architecture_with_bytes

    def racy_loader(path):
        # Atomic read of the OLD bytes...
        parsed, raw = real_loader(path)
        # ...then a concurrent committer overwrites the file before we get
        # to the lock. Our parsed content + raw bytes still reflect the OLD
        # state. The guard must detect that under the lock the on-disk
        # bytes have changed.
        path.write_bytes(other_arch_bytes)
        return parsed, raw

    monkeypatch.setattr(ipa, "_load_architecture_with_bytes", racy_loader)

    add_audit = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_logger_python.prompt",
                reason="audit",
                interface={"type": "module"},
            )
        ],
    )
    monkeypatch.setattr(ipa, "_ask_llm_for_patch", lambda **_: (add_audit, 0.05, "A"))
    monkeypatch.setattr(ipa, "detect_change", lambda *_, **__: ([], 0.0, "A"))

    success, message, _, _, changed = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        project_root=tmp_path,
        quiet=True,
    )

    assert success is False, (
        "Run must fail when baseline does not match under-lock state; "
        f"got success with changed_files={changed}"
    )
    assert "Concurrent modification" in message
    # The other writer's content must remain on disk (no clobber).
    arch_after = json.loads(arch_path.read_text(encoding="utf-8"))
    names = {m["filename"] for m in arch_after["modules"]}
    assert "cache_python.prompt" in names, (
        f"Concurrent committer's module was lost; final modules: {names}"
    )
    assert "audit_logger_python.prompt" not in names
    assert not (prompts / "audit_logger_python.prompt").exists()
    assert not (tmp_path / ".pdd" / "meta" / "prd_hashes.json").exists()


def test_concurrent_runs_no_lost_update(tmp_path, monkeypatch):
    """Two propagation runs with the SAME baseline must never both successfully
    overwrite architecture.json — the second must detect concurrent modification
    and fail cleanly without writing prompts or PRD snapshot.

    Regression for codex round-4 finding: lock previously only covered the
    write window, so two concurrent runs could compute patches against the
    same baseline, both pass validation, and the later write would silently
    overwrite the earlier run's added module while leaving its prompt files
    and PRD snapshot orphaned.
    """
    import pdd.incremental_prd_architecture as ipa

    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add audit logging.", encoding="utf-8")

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    arch_path = tmp_path / "architecture.json"
    original_arch = {
        "prd_files": ["docs/prd.md"],
        "modules": [_module("api_router_python.prompt")],
    }
    arch_path.write_text(json.dumps(original_arch, indent=2), encoding="utf-8")
    pre_arch_bytes = arch_path.read_bytes()

    add_audit = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_logger_python.prompt",
                reason="audit",
                interface={"type": "module"},
            )
        ],
    )
    add_cache = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="cache_python.prompt",
                reason="cache",
                interface={"type": "module"},
            )
        ],
    )

    # Phase 1: simulate run A's compute phase. It loads the baseline.
    # Phase 2: run B sneaks in and commits its add_cache patch FIRST.
    # Phase 3: run A enters its commit lock and tries to write add_audit.
    # F13: under the lock, A re-reads architecture.json, sees it differs from
    # its baseline, and refuses to overwrite.

    # Run B (commits first) — uses real propagation, mocked patch + detect_change.
    monkeypatch.setattr(ipa, "_ask_llm_for_patch", lambda **_: (add_cache, 0.05, "B"))
    monkeypatch.setattr(ipa, "detect_change", lambda *_, **__: ([], 0.0, "B"))

    success_b, _, _, _, changed_b = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        project_root=tmp_path,
        quiet=True,
    )
    assert success_b is True
    assert "architecture.json" in changed_b
    arch_after_b = json.loads(arch_path.read_text(encoding="utf-8"))
    assert "cache_python.prompt" in [m["filename"] for m in arch_after_b["modules"]]
    assert (prompts / "cache_python.prompt").exists()
    snapshot_after_b = (tmp_path / ".pdd" / "meta" / "prd_hashes.json").read_text(
        encoding="utf-8"
    )

    # Now simulate run A: load the OLD baseline (pre-B) and try to commit.
    # We do this by manually invoking with a baseline-poisoning monkeypatch:
    # restore architecture.json to the pre-B bytes for the "load" phase, then
    # restore B's bytes BEFORE the lock is acquired so the under-lock re-read
    # surfaces the race.

    # Restore arch.json to pre-B baseline so A's load sees the OLD content,
    # and BUMP the PRD content so A detects a real diff against B's snapshot
    # (otherwise A would early-return "No PRD changes detected" before reaching
    # the lock).
    arch_path.write_bytes(pre_arch_bytes)
    (docs / "prd.md").write_text(
        "Add audit logging.\n\nAlso add request timing.\n", encoding="utf-8"
    )

    real_lock = ipa._architecture_write_lock

    from contextlib import contextmanager

    @contextmanager
    def race_injecting_lock(directory):
        # Just before A acquires the write lock, swap arch.json back to B's
        # bytes — so A's under-lock re-read sees the concurrent modification.
        arch_path.write_bytes(json.dumps(arch_after_b, indent=2).encode("utf-8") + b"\n")
        with real_lock(directory):
            yield

    monkeypatch.setattr(ipa, "_architecture_write_lock", race_injecting_lock)
    monkeypatch.setattr(ipa, "_ask_llm_for_patch", lambda **_: (add_audit, 0.05, "A"))

    success_a, message_a, _, _, changed_a = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        project_root=tmp_path,
        quiet=True,
    )

    # A must fail with the concurrent-modification message
    assert success_a is False
    assert "Concurrent modification" in message_a
    assert changed_a == []

    # B's writes must still be intact
    arch_final = json.loads(arch_path.read_text(encoding="utf-8"))
    final_names = {m["filename"] for m in arch_final["modules"]}
    assert "cache_python.prompt" in final_names, (
        f"B's added module was lost; final modules: {final_names}"
    )
    assert "audit_logger_python.prompt" not in final_names, (
        f"A's add must NOT have landed; final modules: {final_names}"
    )
    # A must NOT have created its prompt file or advanced the snapshot
    assert not (prompts / "audit_logger_python.prompt").exists()
    assert (
        (tmp_path / ".pdd" / "meta" / "prd_hashes.json").read_text(encoding="utf-8")
        == snapshot_after_b
    )


def test_prompt_preview_existing_file_lost_update_is_rejected(tmp_path, monkeypatch):
    """Prompt files read during compute must be rechecked under the write lock."""
    import pdd.incremental_prd_architecture as ipa
    from contextlib import contextmanager

    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Change API reason.", encoding="utf-8")
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    prompt_path = prompts / "api_router_python.prompt"
    original_prompt = "## Requirements\n\n- Route API requests.\n"
    prompt_path.write_text(original_prompt, encoding="utf-8")
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps({"prd_files": ["docs/prd.md"], "modules": [_module("api_router_python.prompt")]}, indent=2),
        encoding="utf-8",
    )

    patch_obj = ArchitecturePatch(
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"description": "API routing with audit metadata."},
                justification="PRD changed API routing requirements.",
            )
        ]
    )
    monkeypatch.setattr(ipa, "_ask_llm_for_patch", lambda **_: (patch_obj, 0.05, "m"))
    monkeypatch.setattr(ipa, "detect_change", lambda *_, **__: ([], 0.0, "m"))

    real_lock = ipa._architecture_write_lock

    @contextmanager
    def racy_lock(directory):
        prompt_path.write_text("human edit during compute\n", encoding="utf-8")
        with real_lock(directory):
            yield

    monkeypatch.setattr(ipa, "_architecture_write_lock", racy_lock)

    success, message, _, _, changed = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        project_root=tmp_path,
        quiet=True,
    )

    assert success is False
    assert "Concurrent modification detected on prompt file" in message
    assert changed == []
    assert prompt_path.read_text(encoding="utf-8") == "human edit during compute\n"
    modules = json.loads(arch_path.read_text(encoding="utf-8"))["modules"]
    assert modules[0]["description"] == "api_router_python.prompt description"


def test_prompt_preview_created_file_lost_update_is_rejected(tmp_path, monkeypatch):
    """A file created after preview computation must not be overwritten."""
    import pdd.incremental_prd_architecture as ipa
    from contextlib import contextmanager

    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add audit logging.", encoding="utf-8")
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps({"prd_files": ["docs/prd.md"], "modules": [_module("api_router_python.prompt")]}, indent=2),
        encoding="utf-8",
    )
    prompt_path = prompts / "audit_logger_python.prompt"

    patch_obj = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_logger_python.prompt",
                reason="Audit event emission",
                interface={"type": "module"},
            )
        ]
    )
    monkeypatch.setattr(ipa, "_ask_llm_for_patch", lambda **_: (patch_obj, 0.05, "m"))
    monkeypatch.setattr(ipa, "detect_change", lambda *_, **__: ([], 0.0, "m"))

    real_lock = ipa._architecture_write_lock

    @contextmanager
    def racy_lock(directory):
        prompt_path.write_text("competing prompt\n", encoding="utf-8")
        with real_lock(directory):
            yield

    monkeypatch.setattr(ipa, "_architecture_write_lock", racy_lock)

    success, message, _, _, changed = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        project_root=tmp_path,
        quiet=True,
    )

    assert success is False
    assert "file was created after this run's compute phase began" in message
    assert changed == []
    assert prompt_path.read_text(encoding="utf-8") == "competing prompt\n"
    names = {
        module["filename"]
        for module in json.loads(arch_path.read_text(encoding="utf-8"))["modules"]
    }
    assert "audit_logger_python.prompt" not in names


def test_removed_module_deletes_prompt_file_transactionally(tmp_path, monkeypatch):
    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Remove audit logging.", encoding="utf-8")
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    prompt_path = prompts / "audit_python.prompt"
    prompt_path.write_text("audit prompt\n", encoding="utf-8")
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps({"prd_files": ["docs/prd.md"], "modules": [_module("audit_python.prompt")]}, indent=2),
        encoding="utf-8",
    )

    patch_obj = ArchitecturePatch(
        modules_to_remove=[
            ModuleRemoval(
                filename="audit_python.prompt",
                justification="The PRD explicitly removed audit logging.",
            )
        ]
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture._ask_llm_for_patch",
        lambda **_: (patch_obj, 0.05, "m"),
    )
    monkeypatch.setattr("pdd.incremental_prd_architecture.detect_change", lambda *_, **__: ([], 0.0, "m"))

    success, message, _, _, changed = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        project_root=tmp_path,
        quiet=True,
    )

    assert success is True, message
    assert "architecture.json" in changed
    assert "prompts/audit_python.prompt" in changed
    assert not prompt_path.exists()
    assert json.loads(arch_path.read_text(encoding="utf-8"))["modules"] == []


def test_local_output_dir_new_prompt_includes_are_target_relative(tmp_path, monkeypatch):
    """Local PRD state can live at repo root while prompt includes must be subproject-relative."""
    service = tmp_path / "service"
    prompts = service / "prompts"
    prompts.mkdir(parents=True)
    (prompts / "database_python.prompt").write_text("database prompt\n", encoding="utf-8")
    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add audit logging.", encoding="utf-8")
    arch_path = service / "architecture.json"
    arch_path.write_text(
        json.dumps({
            "prd_files": ["../docs/prd.md"],
            "modules": [_module("database_python.prompt")],
        }, indent=2),
        encoding="utf-8",
    )

    patch_obj = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_python.prompt",
                reason="Audit event emission",
                dependencies=["database_python.prompt"],
                interface={"type": "module"},
            )
        ]
    )
    monkeypatch.setattr(
        "pdd.incremental_prd_architecture._ask_llm_for_patch",
        lambda **_: (patch_obj, 0.05, "m"),
    )
    monkeypatch.setattr("pdd.incremental_prd_architecture.detect_change", lambda *_, **__: ([], 0.0, "m"))

    success, message, _, _, _ = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        project_root=tmp_path,
        quiet=True,
    )

    assert success is True, message
    body = (prompts / "audit_python.prompt").read_text(encoding="utf-8")
    assert "<include>prompts/database_python.prompt</include>" in body
    assert "<include>service/prompts/database_python.prompt</include>" not in body


def test_commit_phase_holds_lock_through_prompt_writes(tmp_path, monkeypatch):
    """While a run is in the middle of writing prompts, a second run trying to
    enter the commit phase must block on the architecture-directory lock so
    its writes cannot interleave with the first run's rollback path.
    """
    import threading
    import pdd.incremental_prd_architecture as ipa

    lock_acquisitions: List[str] = []
    real_lock = ipa._architecture_write_lock

    from contextlib import contextmanager

    @contextmanager
    def tracking_lock(directory):
        lock_acquisitions.append(f"acquire:{directory}")
        with real_lock(directory):
            lock_acquisitions.append(f"held:{directory}")
            yield
        lock_acquisitions.append(f"release:{directory}")

    monkeypatch.setattr(ipa, "_architecture_write_lock", tracking_lock)

    docs = tmp_path / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add audit logging.", encoding="utf-8")
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps({"prd_files": ["docs/prd.md"],
                    "modules": [_module("api_router_python.prompt")]}, indent=2),
        encoding="utf-8",
    )

    patch_obj = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_logger_python.prompt",
                reason="audit",
                interface={"type": "module"},
            )
        ],
    )
    monkeypatch.setattr(ipa, "_ask_llm_for_patch", lambda **_: (patch_obj, 0.05, "m"))
    monkeypatch.setattr(ipa, "detect_change", lambda *_, **__: ([], 0.0, "m"))

    success, _, _, _, changed_files = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=arch_path,
        prompts_dir=prompts,
        project_root=tmp_path,
        quiet=True,
    )
    assert success is True

    # The lock must have been acquired exactly once and held across the
    # architecture write AND the new-prompt write.
    acquires = [e for e in lock_acquisitions if e.startswith("acquire:")]
    releases = [e for e in lock_acquisitions if e.startswith("release:")]
    assert len(acquires) == 1, f"lock acquired {len(acquires)} times: {lock_acquisitions}"
    assert len(releases) == 1
    # Architecture write happened, prompt was created, all under the SAME lock window
    assert (prompts / "audit_logger_python.prompt").exists()
    assert "architecture.json" in changed_files


def test_new_prompt_includes_resolve_via_preprocess(tmp_path, monkeypatch):
    """End-to-end check: a generated prompt's <include> path must resolve when
    `pdd preprocess` runs from the project root (cwd). Regression for the
    `<include>./dep.prompt</include>` bug where preprocess looked in cwd /
    package_root / repo_root and never found it.
    """
    from pdd.incremental_prd_architecture import _generate_prompt_files_for_new_modules
    from pdd.preprocess import preprocess

    project_root = tmp_path
    prompts_dir = project_root / "prompts"
    prompts_dir.mkdir()
    # Existing dependency prompt
    (prompts_dir / "database_python.prompt").write_text(
        "DATABASE-DEP-CONTENT", encoding="utf-8"
    )

    new_module = ModuleToAdd(
        filename="audit_logger_python.prompt",
        reason="Audit",
        dependencies=["database_python.prompt"],
        interface={"type": "module"},
    )

    previews = _generate_prompt_files_for_new_modules(
        [new_module],
        prompts_dir,
        project_root=project_root,
    )
    assert len(previews) == 1
    new_body = previews[0].after

    # The include must be project-root-relative, not "./..."
    assert "<include>prompts/database_python.prompt</include>" in new_body
    assert "<include>./database_python.prompt</include>" not in new_body

    # Now run preprocess() from cwd=project_root and confirm the include resolves
    monkeypatch.chdir(project_root)
    expanded = preprocess(new_body, recursive=False, double_curly_brackets=False)
    assert "DATABASE-DEP-CONTENT" in expanded, (
        f"preprocess failed to resolve include path; expanded text was: {expanded[:400]!r}"
    )
    assert "[File not found" not in expanded
