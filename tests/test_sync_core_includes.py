"""Conformance tests for the parser shared by expansion and sync consumers."""

from pdd.preprocess import compute_user_intent_paths
from pathlib import PurePosixPath

import pytest

from pdd.sync_core import (
    IncludeGraphError,
    IncludeSyntax,
    PathPolicy,
    build_include_closure,
    parse_include_references,
)
from pdd.sync_order import extract_includes_from_file


PROMPT = """
<include>docs/a.md</include>
<include path="docs/b.md" select="Thing" optional />
<include query="summarize">docs/c.md</include>
<include-many expand>
docs/d.md, docs/e.md
docs/f.md
</include-many>
```<docs/g.md>```
"""


def test_all_include_grammars_produce_typed_ordered_records() -> None:
    references = parse_include_references(PROMPT)
    assert [item.path for item in references] == [
        "docs/a.md",
        "docs/b.md",
        "docs/c.md",
        "docs/d.md",
        "docs/e.md",
        "docs/f.md",
        "docs/g.md",
    ]
    assert references[1].select == "Thing"
    assert references[1].optional is True
    assert references[2].query == "summarize"
    assert all(item.expand_dependencies for item in references[3:6])
    assert references[-1].syntax is IncludeSyntax.BACKTICK


def test_path_attribute_takes_precedence_over_body() -> None:
    reference = parse_include_references(
        '<include path="docs/source.md">docs/fallback.md</include>'
    )
    assert [item.path for item in reference] == ["docs/source.md"]


def test_literal_include_tag_in_prose_does_not_consume_later_markup() -> None:
    text = (
        "The `<include>` graph is recursive and may mention `<web>` in prose.\n"
        "<include>docs/actual.md</include>\n"
    )
    references = parse_include_references(text)
    assert [item.path for item in references] == ["docs/actual.md"]


def test_preprocess_and_sync_order_use_the_same_parser(tmp_path) -> None:
    prompt = tmp_path / "widget_python.prompt"
    prompt.write_text(PROMPT, encoding="utf-8")
    expected = {item.path for item in parse_include_references(PROMPT)}
    assert compute_user_intent_paths(PROMPT) == expected
    assert extract_includes_from_file(prompt) == expected


def test_duplicates_are_preserved_in_typed_records() -> None:
    references = parse_include_references(
        "<include>docs/a.md</include><include>docs/a.md</include>"
    )
    assert len(references) == 2
    assert references[0].position < references[1].position


def test_transitive_closure_hashes_every_input_and_mode(tmp_path) -> None:
    (tmp_path / "prompts").mkdir()
    (tmp_path / "docs").mkdir()
    (tmp_path / "prompts/widget.prompt").write_text(
        "<include>docs/a.md</include>", encoding="utf-8"
    )
    (tmp_path / "docs/a.md").write_text(
        "<include>docs/b.md</include>", encoding="utf-8"
    )
    (tmp_path / "docs/b.md").write_text("leaf\n", encoding="utf-8")
    closure = build_include_closure(
        PurePosixPath("prompts/widget.prompt"), PathPolicy(tmp_path)
    )
    assert [item.relpath.as_posix() for item in closure.artifacts] == [
        "docs/a.md",
        "docs/b.md",
    ]
    assert len(closure.digest()) == 64


def test_include_cycle_is_an_error(tmp_path) -> None:
    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts/a.prompt").write_text(
        "<include>prompts/b.md</include>", encoding="utf-8"
    )
    (tmp_path / "prompts/b.md").write_text(
        "<include>prompts/a.prompt</include>", encoding="utf-8"
    )
    with pytest.raises(IncludeGraphError, match="cycle"):
        build_include_closure(PurePosixPath("prompts/a.prompt"), PathPolicy(tmp_path))


@pytest.mark.parametrize("path", ["/tmp/secret", "../../secret"])
def test_absolute_and_escaping_include_paths_are_rejected(tmp_path, path) -> None:
    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts/a.prompt").write_text(
        f"<include>{path}</include>", encoding="utf-8"
    )
    with pytest.raises(IncludeGraphError):
        build_include_closure(PurePosixPath("prompts/a.prompt"), PathPolicy(tmp_path))


def test_optional_missing_include_is_bound_but_not_failed(tmp_path) -> None:
    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts/a.prompt").write_text(
        '<include optional path="missing.md" />', encoding="utf-8"
    )
    closure = build_include_closure(
        PurePosixPath("prompts/a.prompt"), PathPolicy(tmp_path)
    )
    assert closure.edges[0].target_exists is False
    assert closure.artifacts == ()


def test_query_include_marks_closure_nondeterministic(tmp_path) -> None:
    (tmp_path / "prompts").mkdir()
    (tmp_path / "docs").mkdir()
    (tmp_path / "docs/a.md").write_text("source\n", encoding="utf-8")
    (tmp_path / "prompts/a.prompt").write_text(
        '<include query="summarize">docs/a.md</include>', encoding="utf-8"
    )
    closure = build_include_closure(
        PurePosixPath("prompts/a.prompt"), PathPolicy(tmp_path)
    )
    assert closure.has_nondeterministic_query is True


def test_relative_include_normalizes_only_after_source_join(tmp_path) -> None:
    prompt = tmp_path / "prompts/project/pages/widget.prompt"
    context = tmp_path / "prompts/project/context/preamble.prompt"
    prompt.parent.mkdir(parents=True)
    context.parent.mkdir(parents=True)
    prompt.write_text("<include>../context/preamble.prompt</include>")
    context.write_text("context\n")
    closure = build_include_closure(
        PurePosixPath("prompts/project/pages/widget.prompt"), PathPolicy(tmp_path)
    )
    assert [item.relpath for item in closure.artifacts] == [
        PurePosixPath("prompts/project/context/preamble.prompt")
    ]


def test_include_searches_ancestor_project_roots_deterministically(tmp_path) -> None:
    prompt = tmp_path / "projects/app/prompts/pages/widget.prompt"
    source = tmp_path / "projects/app/src/config.py"
    prompt.parent.mkdir(parents=True)
    source.parent.mkdir(parents=True)
    prompt.write_text("<include>src/config.py</include>")
    source.write_text("VALUE = 1\n")
    closure = build_include_closure(
        PurePosixPath("projects/app/prompts/pages/widget.prompt"), PathPolicy(tmp_path)
    )
    assert closure.artifacts[0].relpath == PurePosixPath("projects/app/src/config.py")


def test_include_many_glob_hashes_every_matching_file(tmp_path) -> None:
    prompt = tmp_path / "prompts/widget.prompt"
    fixtures = tmp_path / "tests/fixtures"
    prompt.parent.mkdir()
    fixtures.mkdir(parents=True)
    prompt.write_text(
        "<include-many>tests/fixtures/*.yaml</include-many>", encoding="utf-8"
    )
    (fixtures / "a.yaml").write_text("a: 1\n")
    (fixtures / "b.yaml").write_text("b: 2\n")
    closure = build_include_closure(
        PurePosixPath("prompts/widget.prompt"), PathPolicy(tmp_path)
    )
    assert [item.relpath.as_posix() for item in closure.artifacts] == [
        "tests/fixtures/a.yaml",
        "tests/fixtures/b.yaml",
    ]


def test_prompt_tree_projects_include_to_generated_project_tree(tmp_path) -> None:
    prompt = tmp_path / "prompts/frontend/app/widget.prompt"
    config = tmp_path / "frontend/tsconfig.json"
    prompt.parent.mkdir(parents=True)
    config.parent.mkdir()
    prompt.write_text("<include>tsconfig.json</include>")
    config.write_text("{}\n")
    closure = build_include_closure(
        PurePosixPath("prompts/frontend/app/widget.prompt"), PathPolicy(tmp_path)
    )
    assert closure.artifacts[0].relpath == PurePosixPath("frontend/tsconfig.json")


def test_manifest_output_alias_resolves_generated_code_relative_include(tmp_path) -> None:
    prompt = tmp_path / "prompts/frontend/components/widget.prompt"
    dependency = tmp_path / "frontend/src/context/AuthContext.tsx"
    prompt.parent.mkdir(parents=True)
    dependency.parent.mkdir(parents=True)
    prompt.write_text("<include>../context/AuthContext.tsx</include>")
    dependency.write_text("export const AuthContext = {};\n")
    closure = build_include_closure(
        PurePosixPath("prompts/frontend/components/widget.prompt"),
        PathPolicy(tmp_path),
        root_aliases=(PurePosixPath("frontend/src/components/widget.tsx"),),
    )
    assert closure.artifacts[0].relpath == PurePosixPath(
        "frontend/src/context/AuthContext.tsx"
    )


def test_parent_prefixed_repository_path_stays_inside_checkout(tmp_path) -> None:
    prompt = tmp_path / "prompts/frontend/components/widget.prompt"
    dependency = tmp_path / "frontend/src/context/AuthContext.tsx"
    prompt.parent.mkdir(parents=True)
    dependency.parent.mkdir(parents=True)
    prompt.write_text("<include>../../frontend/src/context/AuthContext.tsx</include>")
    dependency.write_text("export const AuthContext = {};\n")
    closure = build_include_closure(
        PurePosixPath("prompts/frontend/components/widget.prompt"),
        PathPolicy(tmp_path),
    )
    assert closure.artifacts[0].relpath == PurePosixPath(
        "frontend/src/context/AuthContext.tsx"
    )


def test_unresolved_external_package_forces_nondeterministic_closure(tmp_path) -> None:
    prompt = tmp_path / "prompts/widget.prompt"
    prompt.parent.mkdir()
    prompt.write_text("<include>next/navigation</include>")
    closure = build_include_closure(
        PurePosixPath("prompts/widget.prompt"), PathPolicy(tmp_path)
    )
    assert closure.artifacts == ()
    assert closure.edges[0].target_exists is False
    assert closure.has_nondeterministic_query is True
