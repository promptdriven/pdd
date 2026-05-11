"""
Test plan for pdd/update_main.py (mirrors the spec's requirements):

Requirements coverage
=====================
R1. update_main signature & return type (tuple or None).
R2. Returns None on error.
R3. Agentic routing: when simple=False and agents available, try agentic
    first, fall back to legacy on failure.
R4. After successful agentic update, prompt content is re-read.
R5. Pulls verbose/quiet/time from ctx.obj.
R6. Strength/temperature resolution: explicit param overrides ctx.obj,
    and ctx.obj is updated with the resolved values.
R7. Empty prompt produced by legacy path is rejected.
R8. Without --output, the input prompt file is overwritten.
R9. use_git + input_code_file is rejected (mutual exclusion).
R10. Legacy path output is run through sanitize_prompt_output before write.
R11. save_fingerprint is invoked on each successful update path, and the
     update succeeds even if save_fingerprint raises (best-effort).

Modes
=====
M1. True update with --use-git -> calls git_update.
M2. True update with --input-code-file -> calls update_prompt with
    original + modified code.
M3. Regeneration mode (only modified_code_file): empty prompt path triggers
    update_prompt with <GENERATE_FROM_CODE> sentinel.
M4. Repo mode end-to-end smoke test.

Helpers
=======
H1. _extract_template_vars reverse-matches a path against a template
    (incl. repeated variables via backreferences).
H2. resolve_prompt_code_pair creates parent dirs and empty prompt file.
H3. _resolve_existing_prompt_path_case_insensitive preserves on-disk case.
H4. _has_skip_suffix detects test/spec/config/setup/stories/d suffixes.
H5. _has_meaningful_code returns False for blank/comment-only files.
H6. _load_pddignore returns patterns and root, stopping at git root.
H7. _is_pddignored matches basename glob, relative-path glob, dir-prefix.
H8. get_language returns expected language by extension; None for unknown.
H9. derive_basename_and_language uses rel-path-without-ext as basename.
H10. get_git_changed_files combines merge-base, uncommitted, staged,
     untracked.
H11. _check_include_deps_changed detects missing/changed deps.
H12. is_code_changed prefers fingerprint over git changed set.
H13. find_and_resolve_all_pairs applies multi-layer exclusions.
H14. _find_prd_file finds conventional PRD filenames.
H15. update_file_pair returns dict with required keys, supports agentic
     and legacy paths.
H16. Repo mode returns None when no eligible code files exist.
H17. Repo mode returns None when no changes detected and no empty prompts.
H18. Empty prompt file in repo mode is always included for update.

Error handling
==============
E1. click.Abort is re-raised.
E2. ValueError surfaces as None return (printed via Rich console).
"""

from __future__ import annotations

import hashlib
import os
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple
from unittest.mock import MagicMock, patch

import click
import pytest

# Ensure repo-root import works regardless of cwd.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from pdd import update_main as um  # noqa: E402
from pdd.update_main import (  # noqa: E402
    _check_include_deps_changed,
    _extract_template_vars,
    _find_prd_file,
    _has_meaningful_code,
    _has_skip_suffix,
    _is_pddignored,
    _load_pddignore,
    _resolve_existing_prompt_path_case_insensitive,
    derive_basename_and_language,
    find_and_resolve_all_pairs,
    get_git_changed_files,
    get_language,
    is_code_changed,
    resolve_prompt_code_pair,
    update_file_pair,
    update_main,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------
def _make_ctx(**overrides) -> click.Context:
    ctx = click.Context(click.Command("update"))
    ctx.obj = {
        "strength": 0.5,
        "temperature": 0.0,
        "verbose": False,
        "quiet": True,
        "time": 0.25,
        "force": True,
        "context": None,
        "confirm_callback": None,
    }
    ctx.obj.update(overrides)
    return ctx


@pytest.fixture
def ctx() -> click.Context:
    return _make_ctx()


# ---------------------------------------------------------------------------
# H1: _extract_template_vars
# ---------------------------------------------------------------------------
class TestExtractTemplateVars:
    def test_simple_match(self):
        out = _extract_template_vars("src/api/handler.py", "src/{category}/{name}.py")
        assert out == {"category": "api", "name": "handler"}

    def test_no_match_returns_none(self):
        assert _extract_template_vars("foo/bar.py", "src/{x}.py") is None

    def test_no_vars_in_template_equal(self):
        assert _extract_template_vars("a/b.py", "a/b.py") == {}

    def test_no_vars_in_template_differ(self):
        assert _extract_template_vars("a/b.py", "a/c.py") is None

    def test_empty_template_returns_none(self):
        assert _extract_template_vars("foo", "") is None

    def test_repeated_variable_backreference(self):
        # Repeated {name} must match identical text via backreference.
        ok = _extract_template_vars("src/foo/foo.py", "src/{name}/{name}.py")
        assert ok == {"name": "foo"}
        bad = _extract_template_vars("src/foo/bar.py", "src/{name}/{name}.py")
        assert bad is None


# ---------------------------------------------------------------------------
# H2/H3: resolve_prompt_code_pair / case-insensitive preservation
# ---------------------------------------------------------------------------
class TestResolvePromptCodePair:
    def test_creates_prompt_path_and_empty_file(self, tmp_path: Path):
        (tmp_path / ".git").mkdir()
        code_file = tmp_path / "src" / "calc.py"
        code_file.parent.mkdir(parents=True)
        code_file.write_text("def f(): pass\n")

        prompt_path, code_path = resolve_prompt_code_pair(code_file, quiet=True)

        assert code_path == code_file.resolve()
        assert prompt_path.name == "calc_python.prompt"
        assert prompt_path.exists()  # touched
        assert prompt_path.parent.exists()

    def test_preserves_existing_case_insensitive_filename(self, tmp_path: Path):
        prompts = tmp_path / "prompts"
        prompts.mkdir()
        existing = prompts / "Calc_Python.prompt"
        existing.write_text("hello")

        target = prompts / "calc_python.prompt"
        result = _resolve_existing_prompt_path_case_insensitive(target)
        assert result == existing


# ---------------------------------------------------------------------------
# H4/H5: skip suffix / meaningful code
# ---------------------------------------------------------------------------
class TestSkipDetection:
    @pytest.mark.parametrize("name", [
        "foo.test.py", "bar.spec.js", "thing.stories.tsx",
        "x.config.js", "y.setup.ts", "z.d.ts",
    ])
    def test_skip_suffix_true(self, name):
        assert _has_skip_suffix(Path(name)) is True

    @pytest.mark.parametrize("name", ["module.py", "service.ts", "main.go"])
    def test_skip_suffix_false(self, name):
        assert _has_skip_suffix(Path(name)) is False

    def test_meaningful_code_true(self, tmp_path: Path):
        f = tmp_path / "a.py"
        f.write_text("# header\n\ndef x(): return 1\n")
        assert _has_meaningful_code(f) is True

    def test_meaningful_code_false_blank_only(self, tmp_path: Path):
        f = tmp_path / "b.py"
        f.write_text("\n   \n\t\n")
        assert _has_meaningful_code(f) is False

    def test_meaningful_code_false_comments_only(self, tmp_path: Path):
        f = tmp_path / "c.py"
        f.write_text("# header\n# nothing else\n")
        assert _has_meaningful_code(f) is False


# ---------------------------------------------------------------------------
# H6/H7: .pddignore
# ---------------------------------------------------------------------------
class TestPddignore:
    def test_load_pddignore(self, tmp_path: Path):
        (tmp_path / ".git").mkdir()
        (tmp_path / ".pddignore").write_text("# c\nignore_me.py\nvendor/\n")
        patterns, root = _load_pddignore(tmp_path)
        assert "ignore_me.py" in patterns
        assert "vendor/" in patterns
        assert root == tmp_path.resolve()

    def test_load_pddignore_missing(self, tmp_path: Path):
        (tmp_path / ".git").mkdir()
        patterns, root = _load_pddignore(tmp_path)
        assert patterns == []
        assert root is None

    def test_is_pddignored_basename_glob(self, tmp_path: Path):
        f = tmp_path / "secret.py"
        f.write_text("x")
        assert _is_pddignored(f, tmp_path, ["secret.py"]) is True
        assert _is_pddignored(f, tmp_path, ["other.py"]) is False

    def test_is_pddignored_directory(self, tmp_path: Path):
        (tmp_path / "vendor").mkdir()
        f = tmp_path / "vendor" / "lib.py"
        f.write_text("x")
        assert _is_pddignored(f, tmp_path, ["vendor/"]) is True

    def test_is_pddignored_relative_glob(self, tmp_path: Path):
        (tmp_path / "src").mkdir()
        f = tmp_path / "src" / "thing.py"
        f.write_text("x")
        assert _is_pddignored(f, tmp_path, ["src/*.py"]) is True

    def test_is_pddignored_empty_patterns(self, tmp_path: Path):
        f = tmp_path / "x.py"
        f.write_text("x")
        assert _is_pddignored(f, tmp_path, []) is False
        assert _is_pddignored(f, None, ["x.py"]) is False


# ---------------------------------------------------------------------------
# H8: language map
# ---------------------------------------------------------------------------
class TestLanguageMap:
    @pytest.mark.parametrize("ext,lang", [
        (".py", "python"),
        (".ts", "typescript"),
        (".js", "javascript"),
        (".go", "go"),
    ])
    def test_known_languages(self, ext, lang):
        assert get_language(Path(f"x{ext}")) == lang

    def test_unknown_returns_none(self):
        assert get_language(Path("foo.xyz")) is None


# ---------------------------------------------------------------------------
# H9: derive_basename_and_language
# ---------------------------------------------------------------------------
class TestDeriveBasename:
    def test_basename_uses_relpath(self, tmp_path: Path):
        f = tmp_path / "src" / "api" / "handler.py"
        f.parent.mkdir(parents=True)
        f.write_text("x")
        basename, lang = derive_basename_and_language(f, tmp_path)
        assert basename == "src_api_handler"
        assert lang == "python"

    def test_outside_repo_root_uses_filename(self, tmp_path: Path):
        # Provide a code path that's not under the repo_root
        outside = tmp_path / "alone.py"
        outside.write_text("x")
        other_root = tmp_path / "other"
        other_root.mkdir()
        basename, lang = derive_basename_and_language(outside, other_root)
        assert basename == "alone"
        assert lang == "python"


# ---------------------------------------------------------------------------
# H10: get_git_changed_files
# ---------------------------------------------------------------------------
class TestGetGitChangedFiles:
    def test_combines_sources(self, tmp_path: Path):
        def fake_run(cmd, **kwargs):
            res = MagicMock()
            res.returncode = 0
            res.stdout = ""
            args = list(cmd)
            if "merge-base" in args:
                res.stdout = "abc\n"
            elif "diff" in args:
                if "abc" in args:
                    res.stdout = "a.py\n"
                elif "--staged" in args:
                    res.stdout = "b.py\n"
                else:
                    res.stdout = "c.py\n"
            elif "ls-files" in args:
                res.stdout = "d.py\n"
            return res

        with patch("pdd.update_main.subprocess.run", side_effect=fake_run):
            changed = get_git_changed_files(tmp_path, "main")

        names = {Path(p).name for p in changed}
        assert names == {"a.py", "b.py", "c.py", "d.py"}

    def test_empty_when_git_unavailable(self, tmp_path: Path):
        def fake_run(cmd, **kwargs):
            raise FileNotFoundError("no git")

        with patch("pdd.update_main.subprocess.run", side_effect=fake_run):
            changed = get_git_changed_files(tmp_path, "main")
        assert changed == set()


# ---------------------------------------------------------------------------
# H11/H12: fingerprint / is_code_changed
# ---------------------------------------------------------------------------
class TestIsCodeChanged:
    def test_no_fingerprint_in_git_set(self, tmp_path: Path):
        f = tmp_path / "m.py"
        f.write_text("def x(): pass\n")
        with patch("pdd.update_main._load_fingerprint", return_value=None):
            changed, reason = is_code_changed(
                f, tmp_path, {str(f.resolve())}
            )
        assert changed is True
        assert "git" in reason

    def test_no_fingerprint_not_in_git_set(self, tmp_path: Path):
        f = tmp_path / "m.py"
        f.write_text("def x(): pass\n")
        with patch("pdd.update_main._load_fingerprint", return_value=None):
            changed, _ = is_code_changed(f, tmp_path, set())
        assert changed is False

    def test_fingerprint_matches(self, tmp_path: Path):
        f = tmp_path / "m.py"
        f.write_text("hello\n")
        h = hashlib.sha256(f.read_bytes()).hexdigest()
        with patch(
            "pdd.update_main._load_fingerprint",
            return_value={"code_hash": h, "include_deps": {}},
        ):
            changed, reason = is_code_changed(f, tmp_path, set())
        assert changed is False
        assert "matches" in reason

    def test_fingerprint_mismatches(self, tmp_path: Path):
        f = tmp_path / "m.py"
        f.write_text("hello\n")
        with patch(
            "pdd.update_main._load_fingerprint",
            return_value={"code_hash": "deadbeef", "include_deps": {}},
        ):
            changed, reason = is_code_changed(f, tmp_path, set())
        assert changed is True
        assert "code hash" in reason

    def test_include_deps_changed(self, tmp_path: Path):
        code = tmp_path / "m.py"
        code.write_text("hello\n")
        dep = tmp_path / "dep.txt"
        dep.write_text("dep v1")
        ch = hashlib.sha256(code.read_bytes()).hexdigest()
        # Stale dep hash forces "changed"
        with patch(
            "pdd.update_main._load_fingerprint",
            return_value={
                "code_hash": ch,
                "include_deps": {str(dep): "stale-hash"},
            },
        ):
            changed, reason = is_code_changed(code, tmp_path, set())
        assert changed is True
        assert "include dep" in reason

    def test_check_include_deps_missing(self, tmp_path: Path):
        missing = tmp_path / "ghost.txt"
        changed, reason = _check_include_deps_changed(
            {"include_deps": {str(missing): "abc"}}
        )
        assert changed is True
        assert "missing" in reason

    def test_check_include_deps_empty(self):
        assert _check_include_deps_changed({}) == (False, "")
        assert _check_include_deps_changed(
            {"include_deps": None}
        ) == (False, "")


# ---------------------------------------------------------------------------
# H13: find_and_resolve_all_pairs (multi-layer exclusion)
# ---------------------------------------------------------------------------
class TestFindAndResolveAllPairs:
    def _make_repo(self, root: Path) -> None:
        (root / ".git").mkdir()
        (root / "src").mkdir()
        (root / "src" / "good.py").write_text("def f(): return 1\n")
        # excluded by prefix
        (root / "src" / "test_skip.py").write_text("def t(): pass\n")
        # excluded by *_example suffix
        (root / "src" / "demo_example.py").write_text("x = 1\n")
        # excluded by skip filename
        (root / "jest.config.js").write_text("x")
        # excluded by skip extension
        (root / "README.md").write_text("# hi")
        # excluded by skip suffix
        (root / "src" / "thing.test.js").write_text("x")
        # comment-only file -> excluded
        (root / "src" / "blank.py").write_text("# only\n")

    def test_excludes_non_eligible(self, tmp_path: Path):
        self._make_repo(tmp_path)
        with patch("pdd.update_main._git_ls_files", return_value=None):
            pairs = find_and_resolve_all_pairs(tmp_path, quiet=True)
        assert len(pairs) == 1
        prompt_p, code_p = pairs[0]
        assert code_p.name == "good.py"
        assert prompt_p.name.endswith("_python.prompt")

    def test_extensions_filter(self, tmp_path: Path):
        (tmp_path / ".git").mkdir()
        (tmp_path / "a.py").write_text("def f(): pass\n")
        (tmp_path / "b.ts").write_text("export const x = 1;\n")
        with patch("pdd.update_main._git_ls_files", return_value=None):
            pairs = find_and_resolve_all_pairs(
                tmp_path, quiet=True, extensions=[".py"]
            )
        assert {c.name for _, c in pairs} == {"a.py"}


# ---------------------------------------------------------------------------
# H14: _find_prd_file
# ---------------------------------------------------------------------------
class TestFindPrdFile:
    def test_prd_md(self, tmp_path: Path):
        f = tmp_path / "PRD.md"
        f.write_text("x")
        assert _find_prd_file(tmp_path) == f

    def test_lowercase_prd(self, tmp_path: Path):
        f = tmp_path / "prd.md"
        f.write_text("x")
        assert _find_prd_file(tmp_path) == f

    def test_suffix_prd(self, tmp_path: Path):
        f = tmp_path / "myproj_prd.md"
        f.write_text("x")
        assert _find_prd_file(tmp_path) == f

    def test_missing(self, tmp_path: Path):
        assert _find_prd_file(tmp_path) is None


# ---------------------------------------------------------------------------
# H15: update_file_pair
# ---------------------------------------------------------------------------
class TestUpdateFilePair:
    def test_missing_code_file_returns_error(self, tmp_path: Path, ctx):
        prompt_file = tmp_path / "p.prompt"
        prompt_file.write_text("x")
        code_file = tmp_path / "missing.py"  # not created

        res = update_file_pair(prompt_file, code_file, ctx, repo=True, simple=True)
        assert res["status"] == "error"
        assert "does not exist" in res["error"]
        assert res["cost"] == 0.0

    def test_agentic_success(self, tmp_path: Path, ctx):
        prompt_file = tmp_path / "p.prompt"
        prompt_file.write_text("old prompt")
        code_file = tmp_path / "c.py"
        code_file.write_text("def f(): pass\n")

        with patch(
            "pdd.update_main._try_agentic_update",
            return_value=("new prompt content", 0.07, "mock-agent"),
        ), patch("pdd.update_main._save_fingerprint_safe") as save_fp:
            res = update_file_pair(
                prompt_file, code_file, ctx, repo=True, simple=False,
            )

        assert res["status"].startswith("updated (agentic)")
        assert res["cost"] == 0.07
        assert res["model"] == "mock-agent"
        save_fp.assert_called_once()

    def test_legacy_existing_prompt_uses_git_update(self, tmp_path: Path, ctx):
        prompt_file = tmp_path / "p.prompt"
        prompt_file.write_text("% existing prompt")
        code_file = tmp_path / "c.py"
        code_file.write_text("def f(): pass\n")

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.git_update",
            return_value=("% updated prompt", 0.02, "mock-llm"),
        ) as gu, patch(
            "pdd.update_main._save_fingerprint_safe"
        ):
            res = update_file_pair(
                prompt_file, code_file, ctx, repo=True, simple=True,
            )

        assert res["status"] == "updated (legacy)"
        assert res["cost"] == 0.02
        gu.assert_called_once()

    def test_legacy_empty_prompt_uses_update_prompt(self, tmp_path: Path, ctx):
        prompt_file = tmp_path / "p.prompt"
        prompt_file.write_text("")  # empty triggers generation
        code_file = tmp_path / "c.py"
        code_file.write_text("def f(): pass\n")

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.update_prompt",
            return_value=("% new prompt", 0.01, "mock-llm"),
        ) as up_mock, patch(
            "pdd.update_main._save_fingerprint_safe"
        ):
            res = update_file_pair(
                prompt_file, code_file, ctx, repo=True, simple=True,
            )

        assert res["status"] == "updated (legacy)"
        # The sentinel must be used for generation.
        called_kwargs = up_mock.call_args.kwargs
        assert called_kwargs["input_prompt"] == "<GENERATE_FROM_CODE>"

    def test_legacy_empty_result_is_error(self, tmp_path: Path, ctx):
        prompt_file = tmp_path / "p.prompt"
        prompt_file.write_text("% existing")
        code_file = tmp_path / "c.py"
        code_file.write_text("def f(): pass\n")

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.git_update",
            return_value=("", 0.0, "mock-llm"),
        ):
            res = update_file_pair(
                prompt_file, code_file, ctx, repo=True, simple=True,
            )
        assert res["status"] == "error"
        assert "Empty" in res["error"]


# ---------------------------------------------------------------------------
# R1/R2/R7/R8/R9 + M1/M2/M3: update_main core behavior
# ---------------------------------------------------------------------------
class TestUpdateMainCore:
    def _setup_files(self, tmp_path: Path) -> Tuple[Path, Path, Path]:
        prompt = tmp_path / "p.prompt"
        prompt.write_text("% existing prompt")
        code = tmp_path / "c.py"
        code.write_text("def f(): return 2\n")
        orig = tmp_path / "c_orig.py"
        orig.write_text("def f(): return 1\n")
        return prompt, code, orig

    def test_mutual_exclusion(self, tmp_path: Path):
        prompt, code, orig = self._setup_files(tmp_path)
        ctx = _make_ctx()
        result = update_main(
            ctx=ctx,
            input_prompt_file=str(prompt),
            modified_code_file=str(code),
            input_code_file=str(orig),
            output=None,
            use_git=True,
            repo=False,
            extensions=None,
            directory=None,
            strength=None,
            temperature=None,
        )
        assert result is None

    def test_true_update_with_input_code(self, tmp_path: Path):
        prompt, code, orig = self._setup_files(tmp_path)
        ctx = _make_ctx()

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.update_prompt",
            return_value=("% new content", 0.05, "mock-llm"),
        ) as up, patch(
            "pdd.update_main._save_fingerprint_safe"
        ) as save_fp, patch(
            "pdd.update_main.construct_paths"
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(orig),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )

        assert result is not None
        text, cost, model = result
        assert text == "% new content"
        assert cost == 0.05
        assert model == "mock-llm"
        up.assert_called_once()
        save_fp.assert_called_once()
        # R8: input prompt file overwritten in place
        assert prompt.read_text(encoding="utf-8") == "% new content"

    def test_true_update_with_use_git(self, tmp_path: Path):
        prompt, code, _ = self._setup_files(tmp_path)
        ctx = _make_ctx()

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.git_update",
            return_value=("% git-updated", 0.04, "mock-git"),
        ) as gu, patch(
            "pdd.update_main._save_fingerprint_safe"
        ), patch(
            "pdd.update_main.construct_paths"
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=None,
                output=None,
                use_git=True,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )

        assert result is not None
        text, cost, model = result
        assert text == "% git-updated"
        assert cost == 0.04
        assert model == "mock-git"
        gu.assert_called_once()

    def test_true_update_with_output_does_not_overwrite_input(self, tmp_path: Path):
        prompt, code, orig = self._setup_files(tmp_path)
        out = tmp_path / "out.prompt"
        ctx = _make_ctx()

        original_content = prompt.read_text(encoding="utf-8")

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.update_prompt",
            return_value=("% generated", 0.01, "mock-llm"),
        ), patch(
            "pdd.update_main._save_fingerprint_safe"
        ), patch(
            "pdd.update_main.construct_paths"
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(orig),
                output=str(out),
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert result is not None
        assert out.read_text(encoding="utf-8") == "% generated"
        # Input prompt unchanged
        assert prompt.read_text(encoding="utf-8") == original_content

    def test_regeneration_mode_only_code(self, tmp_path: Path):
        (tmp_path / ".git").mkdir()
        code = tmp_path / "module.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx()

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.update_prompt",
            return_value=("% generated", 0.01, "mock-llm"),
        ) as up, patch(
            "pdd.update_main._save_fingerprint_safe"
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=None,
                modified_code_file=str(code),
                input_code_file=None,
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert result is not None
        text, cost, model = result
        assert text == "% generated"
        # sentinel used because new prompt empty
        assert up.call_args.kwargs["input_prompt"] == "<GENERATE_FROM_CODE>"

    def test_empty_prompt_returns_none(self, tmp_path: Path):
        prompt, code, orig = self._setup_files(tmp_path)
        ctx = _make_ctx()

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.update_prompt",
            return_value=("   ", 0.01, "mock-llm"),
        ), patch(
            "pdd.update_main._save_fingerprint_safe"
        ), patch(
            "pdd.update_main.construct_paths"
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(orig),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert result is None
        # original content preserved
        assert prompt.read_text() == "% existing prompt"

    def test_missing_input_returns_none(self):
        ctx = _make_ctx()
        # No input_prompt_file and no use_git/input_code_file
        result = update_main(
            ctx=ctx,
            input_prompt_file=None,
            modified_code_file=None,
            input_code_file=None,
            output=None,
            use_git=False,
            repo=False,
            extensions=None,
            directory=None,
            strength=None,
            temperature=None,
        )
        assert result is None


# ---------------------------------------------------------------------------
# R3/R4: Agentic routing
# ---------------------------------------------------------------------------
class TestAgenticRouting:
    def test_agentic_success_returns_content(self, tmp_path: Path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("% existing")
        code = tmp_path / "c.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx()

        with patch(
            "pdd.update_main._try_agentic_update",
            return_value=("% agentic content", 0.10, "agent-x"),
        ), patch("pdd.update_main._save_fingerprint_safe"), patch(
            "pdd.update_main.construct_paths"
        ), patch("pdd.update_main.update_prompt") as up, patch(
            "pdd.update_main.git_update"
        ) as gu:
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=None,
                output=None,
                use_git=True,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=False,
            )

        assert result is not None
        text, cost, model = result
        assert text == "% agentic content"
        assert cost == 0.10
        assert model == "agent-x"
        # Legacy paths NOT touched on agentic success
        up.assert_not_called()
        gu.assert_not_called()

    def test_agentic_failure_falls_back_to_legacy(self, tmp_path: Path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("% existing")
        code = tmp_path / "c.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx()

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ) as agentic, patch(
            "pdd.update_main.git_update",
            return_value=("% legacy", 0.02, "legacy-llm"),
        ) as gu, patch(
            "pdd.update_main._save_fingerprint_safe"
        ), patch(
            "pdd.update_main.construct_paths"
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=None,
                output=None,
                use_git=True,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=False,
            )
        agentic.assert_called_once()
        gu.assert_called_once()
        assert result is not None
        assert result[0] == "% legacy"

    def test_simple_true_skips_agentic(self, tmp_path: Path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("% existing")
        code = tmp_path / "c.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx()

        with patch("pdd.update_main._try_agentic_update") as agentic, patch(
            "pdd.update_main.git_update",
            return_value=("% legacy", 0.02, "mock-llm"),
        ), patch("pdd.update_main._save_fingerprint_safe"), patch(
            "pdd.update_main.construct_paths"
        ):
            update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=None,
                output=None,
                use_git=True,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        agentic.assert_not_called()


# ---------------------------------------------------------------------------
# R6: strength/temperature resolution
# ---------------------------------------------------------------------------
class TestStrengthTemperatureResolution:
    def test_explicit_overrides_ctx(self, tmp_path: Path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("% existing")
        code = tmp_path / "c.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx(strength=0.1, temperature=0.0)

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.update_prompt",
            return_value=("% out", 0.01, "mock"),
        ) as up, patch(
            "pdd.update_main._save_fingerprint_safe"
        ), patch(
            "pdd.update_main.construct_paths"
        ):
            update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=0.9,
                temperature=0.7,
                simple=True,
            )
        assert up.call_args.kwargs["strength"] == 0.9
        assert up.call_args.kwargs["temperature"] == 0.7
        # ctx.obj updated
        assert ctx.obj["strength"] == 0.9
        assert ctx.obj["temperature"] == 0.7

    def test_falls_back_to_ctx(self, tmp_path: Path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("% existing")
        code = tmp_path / "c.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx(strength=0.42, temperature=0.13)

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.update_prompt",
            return_value=("% out", 0.01, "mock"),
        ) as up, patch(
            "pdd.update_main._save_fingerprint_safe"
        ), patch(
            "pdd.update_main.construct_paths"
        ):
            update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert up.call_args.kwargs["strength"] == 0.42
        assert up.call_args.kwargs["temperature"] == 0.13


# ---------------------------------------------------------------------------
# R10: sanitize_prompt_output applied to legacy writes
# ---------------------------------------------------------------------------
class TestSanitizeOnLegacyWrite:
    def test_sanitize_called(self, tmp_path: Path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("% existing")
        code = tmp_path / "c.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx()

        legacy_output = "% with <include>x</include>"
        sanitized = "% sanitized"

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.update_prompt",
            return_value=(legacy_output, 0.01, "mock"),
        ), patch(
            "pdd.update_main._save_fingerprint_safe"
        ), patch(
            "pdd.update_main.construct_paths"
        ), patch(
            "pdd.update_main.sanitize_prompt_output",
            return_value=(sanitized, []),
        ) as sanitize:
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        sanitize.assert_called_once()
        # First positional arg is the raw legacy content
        args, _ = sanitize.call_args
        assert args[0] == legacy_output
        assert prompt.read_text(encoding="utf-8") == sanitized
        assert result == (sanitized, 0.01, "mock")


# ---------------------------------------------------------------------------
# R11: save_fingerprint best-effort
# ---------------------------------------------------------------------------
class TestSaveFingerprintBestEffort:
    def test_save_fingerprint_called_on_success(self, tmp_path: Path):
        prompt = tmp_path / "p_python.prompt"
        prompt.write_text("% existing")
        code = tmp_path / "p.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx()

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.update_prompt",
            return_value=("% new", 0.01, "mock"),
        ), patch(
            "pdd.update_main.save_fingerprint"
        ) as save_fp, patch(
            "pdd.update_main.infer_module_identity",
            return_value=("p", "python"),
        ), patch(
            "pdd.update_main.construct_paths"
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert result is not None
        save_fp.assert_called_once()

    def test_save_fingerprint_failure_does_not_break_update(self, tmp_path: Path):
        prompt = tmp_path / "p_python.prompt"
        prompt.write_text("% existing")
        code = tmp_path / "p.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx()

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.update_prompt",
            return_value=("% new", 0.01, "mock"),
        ), patch(
            "pdd.update_main.save_fingerprint",
            side_effect=RuntimeError("boom"),
        ), patch(
            "pdd.update_main.infer_module_identity",
            return_value=("p", "python"),
        ), patch(
            "pdd.update_main.construct_paths"
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        # Update still succeeded despite fingerprint failure
        assert result is not None
        assert result[0] == "% new"


# ---------------------------------------------------------------------------
# M4: Repo mode end-to-end
# ---------------------------------------------------------------------------
class TestRepoMode:
    def test_no_files_returns_none(self, tmp_path: Path):
        ctx = _make_ctx()
        with patch(
            "pdd.update_main.find_and_resolve_all_pairs", return_value=[]
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                use_git=False,
                repo=True,
                extensions=None,
                directory=str(tmp_path),
                strength=None,
                temperature=None,
                simple=True,
            )
        assert result is None

    def test_no_changes_returns_none(self, tmp_path: Path):
        (tmp_path / ".git").mkdir()
        prompt = tmp_path / "prompts" / "x_python.prompt"
        prompt.parent.mkdir()
        prompt.write_text("non-empty prompt")
        code = tmp_path / "x.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx()

        with patch(
            "pdd.update_main.find_and_resolve_all_pairs",
            return_value=[(prompt, code)],
        ), patch(
            "pdd.update_main.get_git_changed_files", return_value=set()
        ), patch(
            "pdd.update_main.is_code_changed",
            return_value=(False, "no change"),
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                use_git=False,
                repo=True,
                extensions=None,
                directory=str(tmp_path),
                strength=None,
                temperature=None,
                simple=True,
            )
        assert result is None

    def test_empty_prompt_always_updated(self, tmp_path: Path):
        (tmp_path / ".git").mkdir()
        prompt = tmp_path / "prompts" / "x_python.prompt"
        prompt.parent.mkdir()
        prompt.write_text("")  # empty 0-byte
        code = tmp_path / "x.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx()

        update_result = {
            "prompt_file": str(prompt),
            "code_file": str(code),
            "status": "updated (legacy)",
            "cost": 0.03,
            "model": "mock-llm",
            "error": "",
        }

        with patch(
            "pdd.update_main.find_and_resolve_all_pairs",
            return_value=[(prompt, code)],
        ), patch(
            "pdd.update_main.get_git_changed_files", return_value=set()
        ), patch(
            "pdd.update_main.is_code_changed", return_value=(False, "no")
        ), patch(
            "pdd.update_main.update_file_pair", return_value=update_result
        ) as ufp:
            result = update_main(
                ctx=ctx,
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                use_git=False,
                repo=True,
                extensions=None,
                directory=str(tmp_path),
                strength=None,
                temperature=None,
                simple=True,
            )
        ufp.assert_called_once()
        assert result is not None
        msg, cost, models = result
        assert msg == "Repository update complete."
        assert cost == 0.03
        assert models == "models"

    def test_repo_changed_pair_updates(self, tmp_path: Path):
        (tmp_path / ".git").mkdir()
        prompt = tmp_path / "prompts" / "x_python.prompt"
        prompt.parent.mkdir()
        prompt.write_text("non-empty prompt")
        code = tmp_path / "x.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx()

        update_result = {
            "prompt_file": str(prompt),
            "code_file": str(code),
            "status": "updated (agentic)",
            "cost": 0.08,
            "model": "mock-agent",
            "error": "",
        }

        with patch(
            "pdd.update_main.find_and_resolve_all_pairs",
            return_value=[(prompt, code)],
        ), patch(
            "pdd.update_main.get_git_changed_files",
            return_value={str(code.resolve())},
        ), patch(
            "pdd.update_main.is_code_changed",
            return_value=(True, "changed"),
        ), patch(
            "pdd.update_main.update_file_pair", return_value=update_result
        ) as ufp:
            result = update_main(
                ctx=ctx,
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                use_git=False,
                repo=True,
                extensions=None,
                directory=str(tmp_path),
                strength=None,
                temperature=None,
                simple=True,
            )
        ufp.assert_called_once()
        assert result is not None
        assert result[1] == 0.08


# ---------------------------------------------------------------------------
# E1: click.Abort re-raised
# ---------------------------------------------------------------------------
class TestErrorHandling:
    def test_click_abort_reraised(self, tmp_path: Path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("% existing")
        code = tmp_path / "c.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx()

        with patch(
            "pdd.update_main._try_agentic_update",
            side_effect=click.Abort(),
        ):
            with pytest.raises(click.Abort):
                update_main(
                    ctx=ctx,
                    input_prompt_file=str(prompt),
                    modified_code_file=str(code),
                    input_code_file=str(code),
                    output=None,
                    use_git=False,
                    repo=False,
                    extensions=None,
                    directory=None,
                    strength=None,
                    temperature=None,
                    simple=False,
                )

    def test_unexpected_exception_returns_none(self, tmp_path: Path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("% existing")
        code = tmp_path / "c.py"
        code.write_text("def f(): pass\n")
        ctx = _make_ctx()

        with patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main.update_prompt",
            side_effect=RuntimeError("network down"),
        ), patch(
            "pdd.update_main.construct_paths"
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert result is None
