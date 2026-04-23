"""Tests for auto-deps → architecture.json dependency updates."""
from __future__ import annotations

import json
from pathlib import Path

from pdd.json_atomic import atomic_write_json

from pdd.auto_deps_architecture import (
    extract_include_paths_from_prompt_text,
    merge_auto_deps_includes_into_architecture,
    _minimal_dependencies_array_patch,
    _replace_dependencies_in_architecture_text,
)
from pdd.json_atomic import atomic_write_json


def test_extract_include_paths_supports_attributes() -> None:
    text = '<include path="x">foo/bar.prompt</include>\n<include>plain.prompt</include>'
    paths = extract_include_paths_from_prompt_text(text)
    assert "foo/bar.prompt" in paths
    assert "plain.prompt" in paths


def test_merge_adds_architecture_dependency_for_new_module_include(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "child_Python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "parent_Python.prompt").write_text("%\n", encoding="utf-8")

    arch = [
        {"filename": "child_Python.prompt", "dependencies": []},
        {"filename": "parent_Python.prompt", "dependencies": []},
    ]
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch), encoding="utf-8")

    old = "%\n"
    new = "%\n<include>parent_python.prompt</include>\n"

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "child_Python.prompt",
        old,
        new,
    )
    assert report["updated"] is True
    assert report["added_dependencies"] == ["parent_Python.prompt"]

    data = json.loads(arch_path.read_text(encoding="utf-8"))
    child = next(e for e in data if e["filename"] == "child_Python.prompt")
    assert child["dependencies"] == ["parent_Python.prompt"]


def test_merge_noop_when_prompt_not_in_architecture(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    p = prompts / "solo_Python.prompt"
    p.write_text("%\n", encoding="utf-8")
    (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        p,
        "%\n",
        '%\n<include>other_python.prompt</include>\n',
    )
    assert report["updated"] is False
    assert report["added_dependencies"] == []


def test_merge_ignores_non_module_includes(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "api_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [{"filename": "api_Python.prompt", "dependencies": []}]
    (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "api_Python.prompt",
        "%\n",
        '%\n<include>context/preamble.prompt</include>\n',
    )
    assert report["updated"] is False


def test_merge_idempotent_when_dependency_already_listed(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "a_Python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "b_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "a_Python.prompt", "dependencies": ["b_Python.prompt"]},
        {"filename": "b_Python.prompt", "dependencies": []},
    ]
    ap = tmp_path / "architecture.json"
    ap.write_text(json.dumps(arch), encoding="utf-8")

    old = "%\n"
    new = "%\n<include>b_python.prompt</include>\n"
    report = merge_auto_deps_includes_into_architecture(
        tmp_path, prompts / "a_Python.prompt", old, new
    )
    assert report["updated"] is False
    assert report["added_dependencies"] == []


def test_merge_skips_self_referential_module_include(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "mod_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [{"filename": "mod_Python.prompt", "dependencies": []}]
    (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    old = "%\n"
    new = "%\n<include>mod_python.prompt</include>\n"
    report = merge_auto_deps_includes_into_architecture(
        tmp_path, prompts / "mod_Python.prompt", old, new
    )
    assert report["updated"] is False


def test_merge_dry_run_does_not_write(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "child_Python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "parent_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "child_Python.prompt", "dependencies": []},
        {"filename": "parent_Python.prompt", "dependencies": []},
    ]
    ap = tmp_path / "architecture.json"
    original = json.dumps(arch)
    ap.write_text(original, encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "child_Python.prompt",
        "%\n",
        '%\n<include>parent_python.prompt</include>\n',
        dry_run=True,
    )
    assert report["updated"] is True
    assert ap.read_text(encoding="utf-8") == original
    assert json.loads(ap.read_text(encoding="utf-8"))[0]["dependencies"] == []


def test_merge_resolves_nested_package_architecture(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    svc = tmp_path / "svc"
    pr = svc / "prompts"
    pr.mkdir(parents=True)
    (pr / "a_Python.prompt").write_text("%\n", encoding="utf-8")
    (pr / "b_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "a_Python.prompt", "dependencies": []},
        {"filename": "b_Python.prompt", "dependencies": []},
    ]
    (svc / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        pr / "a_Python.prompt",
        "%\n",
        '%\n<include>b_python.prompt</include>\n',
    )
    assert report["updated"] is True
    data = json.loads((svc / "architecture.json").read_text(encoding="utf-8"))
    a = next(e for e in data if e["filename"] == "a_Python.prompt")
    assert a["dependencies"] == ["b_Python.prompt"]


def test_merge_maps_example_path_include_to_module_arch_entry(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    ctx = tmp_path / "context"
    ctx.mkdir()
    (ctx / "models_example.py").write_text("# x", encoding="utf-8")
    (prompts / "api_Python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "models_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "api_Python.prompt", "dependencies": []},
        {"filename": "models_Python.prompt", "dependencies": []},
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "api_Python.prompt",
        "%\n",
        '%\n<include>context/models_example.py</include>\n',
    )
    assert report["updated"] is True
    assert report["added_dependencies"] == ["models_Python.prompt"]
    data = json.loads((tmp_path / "architecture.json").read_text(encoding="utf-8"))
    api = next(e for e in data if e["filename"] == "api_Python.prompt")
    assert api["dependencies"] == ["models_Python.prompt"]


def test_merge_preserves_text_after_second_entry_when_only_first_changes(tmp_path: Path) -> None:
    """Surgical write must not reformat later architecture entries."""
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "child_Python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "parent_Python.prompt").write_text("%\n", encoding="utf-8")
    raw = """[
  {
    "filename": "child_Python.prompt",
    "dependencies": []
  },
  {
    "filename": "parent_Python.prompt",
    "dependencies": []
  }
]"""
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(raw, encoding="utf-8")

    merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "child_Python.prompt",
        "%\n",
        '%\n<include>parent_python.prompt</include>\n',
    )
    after = arch_path.read_text(encoding="utf-8")
    marker = '"filename": "parent_Python.prompt"'
    assert after[after.find(marker) :] == raw[raw.find(marker) :]


def test_minimal_append_only_inserts_before_closing_bracket() -> None:
    """Suffix-append should leave existing array bytes (except new insert) unchanged."""
    old = """[
      "a.prompt"
    ]"""
    out = _minimal_dependencies_array_patch(old, ["a.prompt", "b.prompt"])
    assert out is not None
    assert out == """[
      "a.prompt",
      "b.prompt"
    ]"""
    # Compact one-line array: only grow before ]
    compact = '["a.prompt"]'
    out_c = _minimal_dependencies_array_patch(compact, ["a.prompt", "b.prompt"])
    assert out_c == '["a.prompt", "b.prompt"]'


def test_replace_dependencies_in_architecture_text_round_trip() -> None:
    raw = """[
  {"filename": "a.prompt", "dependencies": []},
  {"filename": "b.prompt", "dependencies": ["x.prompt"]}
]"""
    out = _replace_dependencies_in_architecture_text(raw, 0, ["b.prompt"])
    assert out is not None
    data = json.loads(out)
    assert data[0]["dependencies"] == ["b.prompt"]
    assert data[1]["dependencies"] == ["x.prompt"]
def test_atomic_write_json_writes_parseable_file(tmp_path: Path) -> None:
    path = tmp_path / "data.json"
    atomic_write_json(path, [{"a": 1}])
    assert path.read_text(encoding="utf-8").strip().startswith("[")


def test_merge_does_not_add_dep_without_architecture_entry_for_peer(tmp_path: Path) -> None:
    """Unknown modules (no row in architecture) are not appended as orphan filenames."""
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "only_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [{"filename": "only_Python.prompt", "dependencies": []}]
    (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "only_Python.prompt",
        "%\n",
        '%\n<include>ghost_python.prompt</include>\n',
    )
    assert report["updated"] is False


# --- Issue #1256: Dict-format architecture tolerance ---
# Scope addition: covers expansion item "pdd/auto_deps_architecture.py:42 loads
# architecture.json with isinstance(data list) check that silently drops dict-format
# data" identified by Step 6 but absent from Step 8's plan


def test_find_architecture_record_dict_format_finds_entry(tmp_path: Path) -> None:
    """_find_architecture_record_for_prompt_file with dict-format architecture finds entry (Test 15).

    Bug: isinstance(data, list) at auto_deps_architecture.py:42 returns False
    for dict-format {"modules": [...]}, so the architecture file is silently
    skipped and the function returns None instead of the matching entry.
    """
    from pdd.auto_deps_architecture import _find_architecture_record_for_prompt_file

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    prompt_file = prompts / "auth_Python.prompt"
    prompt_file.write_text("%\n", encoding="utf-8")

    # Dict-format architecture referencing the prompt file
    arch = {"modules": [
        {"filename": "auth_Python.prompt", "dependencies": []}
    ]}
    (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    result = _find_architecture_record_for_prompt_file(tmp_path, prompt_file)
    assert result is not None, (
        "Dict-format architecture should find the prompt entry, "
        "but isinstance(data, list) at auto_deps_architecture.py:42 silently skips it"
    )


def test_merge_writes_dict_format_architecture_preserving_wrapper(tmp_path: Path) -> None:
    """Surgical dependency patch must work on ``{"prd_files": [...], "modules": [...]}``
    without corrupting the wrapper or silently falling back to no-op.
    """
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "child_Python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "parent_Python.prompt").write_text("%\n", encoding="utf-8")

    raw = """{
  "prd_files": ["docs/prd.md"],
  "modules": [
    {
      "filename": "child_Python.prompt",
      "dependencies": []
    },
    {
      "filename": "parent_Python.prompt",
      "dependencies": []
    }
  ]
}"""
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(raw, encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "child_Python.prompt",
        "%\n",
        "%\n<include>parent_python.prompt</include>\n",
    )
    assert report["updated"] is True
    assert report["added_dependencies"] == ["parent_Python.prompt"]

    after = json.loads(arch_path.read_text(encoding="utf-8"))
    assert isinstance(after, dict), "Dict wrapper must be preserved"
    assert after["prd_files"] == ["docs/prd.md"], "prd_files must be preserved"
    modules = after["modules"]
    assert len(modules) == 2
    child = next(m for m in modules if m["filename"] == "child_Python.prompt")
    assert child["dependencies"] == ["parent_Python.prompt"]


def test_replace_dependencies_in_dict_format_round_trip() -> None:
    """_replace_dependencies_in_architecture_text handles dict wrapper surgically."""
    raw = """{
  "prd_files": [],
  "modules": [
    {"filename": "a.prompt", "dependencies": []},
    {"filename": "b.prompt", "dependencies": ["x.prompt"]}
  ]
}"""
    out = _replace_dependencies_in_architecture_text(raw, 0, ["b.prompt"])
    assert out is not None, "Dict-format architecture must be patchable in place"
    data = json.loads(out)
    assert isinstance(data, dict)
    assert data["modules"][0]["dependencies"] == ["b.prompt"]
    assert data["modules"][1]["dependencies"] == ["x.prompt"]
    assert "prd_files" in data, "prd_files wrapper key must survive the patch"


def test_find_modules_array_start_handles_both_shapes() -> None:
    """_find_modules_array_start must handle bare-array and dict wrapper; reject unknown shapes."""
    from pdd.auto_deps_architecture import _find_modules_array_start

    bare = '[{"filename": "a.prompt"}]'
    assert _find_modules_array_start(bare) == bare.find("[")

    wrapped = '{"prd_files": [], "modules": [{"filename": "a.prompt"}]}'
    # must point at the `[` that opens "modules", not the empty prd_files `[`
    modules_bracket = wrapped.find('"modules":') + len('"modules":')
    while wrapped[modules_bracket] in " \t":
        modules_bracket += 1
    assert _find_modules_array_start(wrapped) == modules_bracket

    unknown = '{"foo": [1, 2]}'
    assert _find_modules_array_start(unknown) == -1
    assert _find_modules_array_start("   42") == -1
    assert _find_modules_array_start("") == -1
