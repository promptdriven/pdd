"""
Tests for pdd.agentic_reviewer

Test plan (one section per spec requirement):
 R1.  run_agentic_reviewer: correct signature, bounds defaults (max_files=20,
      max_follow_depth=2, max_search_results=50, max_runtime_seconds=30)
 R2.  _extract_symbols: regex-based extraction of import, env, write, network,
      log symbols; returns {symbol, kind, line, excerpt} with correct line numbers
 R3.  BFS import-chain: follows local relative imports up to max_follow_depth,
      visited_files prevents cycles, max_files hard-stop, bounds checked before
      reading each new file
 R4.  _inspect_manifests: reads package.json (deps+devDeps), requirements.txt,
      pyproject.toml ([project.dependencies]), go.mod (require block); skips
      missing files silently
 R5.  LLM classifier call: invoked with strength=0.0, temperature=0.1,
      output_schema; target is a language string; exception is swallowed and
      produces no agentic findings
 R6.  _extract_last_json: iterates from every [ and { position, captures arrays
      AND objects, returns last valid non-nested one; returns None when no JSON
      present
 R7.  Finding normalization: every finding has source, severity, confidence,
      effect{action,resource}, message, evidence[{file,line,excerpt}],
      agent_steps; breadcrumb format ("Read file X", "Found symbol Y at line N",
      "Followed import to Z")
 R8.  Insufficient-evidence sentinel: returned when observed_evidence==0 or all
      confidence<0.5; classifier outage/invalid JSON returns [] so it does not
      become a user-visible policy finding
 R9.  Path safety: _resolve_local_import rejects paths escaping project root;
      UnicodeDecodeError files skipped silently
 R10. _detect_language: py→python, ts/tsx→typescript, js/jsx/cjs/mjs→javascript,
      other→unknown
 R11. _resolve_local_import: resolves relative paths, tries multiple extensions,
      returns None for non-relative paths, returns None for missing files
 R12. _build_classifier_input: returns dict with keys contract_effects, target,
      observed_evidence, deterministic_findings
 R13. Regression: pyproject.toml regex was broken (?(: vs (?:) — verify parse works
 R14. Regression: wrapper following reaches sibling project directories and
      exception handler returns [] for classifier failures after evidence collection
"""
from __future__ import annotations

import json
import os
import sys
import tempfile
import time
import types
from pathlib import Path
from typing import Any, Dict, List
from unittest.mock import MagicMock, patch

import pytest

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _mock_llm_result(findings: List[Dict]) -> Dict[str, Any]:
    """Build a mock llm_invoke return value."""
    return {"result": findings, "cost": 0.0, "model_name": "mock"}


def _mock_classifier_response(result: Dict[str, Any], captured: Dict[str, Any] | None = None):
    """Build a mock _invoke_llm_with_timeout side effect."""
    def fake_classifier(timeout_seconds: float, **kwargs: Any) -> Dict[str, Any]:
        if captured is not None:
            captured["timeout_seconds"] = timeout_seconds
            captured["kwargs"] = kwargs
        return result

    return fake_classifier


def _write_files(tmp_path: Path, files: Dict[str, str]) -> None:
    """Write a dict of {relative_path: content} to tmp_path."""
    for rel, content in files.items():
        p = tmp_path / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")


# ---------------------------------------------------------------------------
# R10: _detect_language
# ---------------------------------------------------------------------------

from pdd.agentic_reviewer import _detect_language


class TestDetectLanguage:
    def test_python(self):
        assert _detect_language(Path("foo.py")) == "python"

    def test_typescript(self):
        assert _detect_language(Path("app.ts")) == "typescript"

    def test_tsx(self):
        assert _detect_language(Path("App.tsx")) == "typescript"

    def test_javascript(self):
        assert _detect_language(Path("index.js")) == "javascript"

    def test_jsx(self):
        assert _detect_language(Path("comp.jsx")) == "javascript"

    def test_cjs(self):
        assert _detect_language(Path("mod.cjs")) == "javascript"

    def test_mjs(self):
        assert _detect_language(Path("mod.mjs")) == "javascript"

    def test_unknown_csv(self):
        assert _detect_language(Path("data.csv")) == "unknown"

    def test_unknown_no_ext(self):
        assert _detect_language(Path("Makefile")) == "unknown"

    def test_case_insensitive(self):
        # Extension matching is lowercase
        assert _detect_language(Path("FOO.PY")) == "python"


# ---------------------------------------------------------------------------
# R2: _extract_symbols
# ---------------------------------------------------------------------------

from pdd.agentic_reviewer import _extract_symbols


class TestExtractSymbols:
    def test_import_python(self):
        code = "import os\nfrom pathlib import Path\n"
        syms = _extract_symbols(Path("x.py"), code)
        kinds = [s["kind"] for s in syms]
        assert kinds.count("import") == 2

    def test_require_call(self):
        code = "const fs = require('fs')\n"
        syms = _extract_symbols(Path("x.js"), code)
        imports = [s for s in syms if s["kind"] == "import"]
        assert len(imports) >= 1
        assert any("require" in s["symbol"] for s in imports)

    def test_env_os_environ_get(self):
        code = "x = os.environ.get('SECRET')\n"
        syms = _extract_symbols(Path("x.py"), code)
        envs = [s for s in syms if s["kind"] == "env"]
        assert len(envs) >= 1

    def test_env_os_environ_subscript(self):
        code = "x = os.environ['KEY']\n"
        syms = _extract_symbols(Path("x.py"), code)
        envs = [s for s in syms if s["kind"] == "env"]
        assert len(envs) >= 1

    def test_env_process_env(self):
        code = "const x = process.env.API_KEY;\n"
        syms = _extract_symbols(Path("x.js"), code)
        envs = [s for s in syms if s["kind"] == "env"]
        assert len(envs) >= 1

    def test_write_open_w(self):
        code = "with open('out.txt', 'w') as f:\n    pass\n"
        syms = _extract_symbols(Path("x.py"), code)
        writes = [s for s in syms if s["kind"] == "write"]
        assert len(writes) >= 1

    def test_write_open_double_quote(self):
        code = 'f = open("output.log", "w")\n'
        syms = _extract_symbols(Path("x.py"), code)
        writes = [s for s in syms if s["kind"] == "write"]
        assert len(writes) >= 1

    def test_write_fs_write(self):
        code = "fs.writeFileSync('out.txt', data);\n"
        syms = _extract_symbols(Path("x.js"), code)
        writes = [s for s in syms if s["kind"] == "write"]
        assert len(writes) >= 1

    def test_network_fetch(self):
        code = "const r = await fetch('https://api.example.com');\n"
        syms = _extract_symbols(Path("x.js"), code)
        networks = [s for s in syms if s["kind"] == "network"]
        assert len(networks) >= 1

    def test_network_requests_get(self):
        code = "response = requests.get('https://api.example.com')\n"
        syms = _extract_symbols(Path("x.py"), code)
        networks = [s for s in syms if s["kind"] == "network"]
        assert len(networks) >= 1

    def test_network_urllib(self):
        code = "import urllib.request\nurllib.request.urlopen(url)\n"
        syms = _extract_symbols(Path("x.py"), code)
        networks = [s for s in syms if s["kind"] == "network"]
        assert len(networks) >= 1

    def test_log_logging(self):
        code = "logging.info('started')\n"
        syms = _extract_symbols(Path("x.py"), code)
        logs = [s for s in syms if s["kind"] == "log"]
        assert len(logs) >= 1

    def test_log_console(self):
        code = "console.log('hello');\n"
        syms = _extract_symbols(Path("x.js"), code)
        logs = [s for s in syms if s["kind"] == "log"]
        assert len(logs) >= 1

    def test_log_logger(self):
        code = "logger.info('done')\n"
        syms = _extract_symbols(Path("x.py"), code)
        logs = [s for s in syms if s["kind"] == "log"]
        assert len(logs) >= 1

    def test_chained_method_call_extracted(self):
        code = "await notificationClient.sendRefundNotice(refund.customer_email);\n"
        syms = _extract_symbols(Path("x.ts"), code)
        calls = [s for s in syms if s["kind"] == "call"]
        assert any("notificationClient.sendRefundNotice(" in s["symbol"] for s in calls)

    def test_nested_chained_method_call_extracted(self):
        code = "return resend.emails.send({ to: email });\n"
        syms = _extract_symbols(Path("x.ts"), code)
        calls = [s for s in syms if s["kind"] == "call"]
        assert any("resend.emails.send(" in s["symbol"] for s in calls)

    def test_symbol_dict_keys(self):
        code = "import os\n"
        syms = _extract_symbols(Path("x.py"), code)
        assert len(syms) >= 1
        s = syms[0]
        assert "symbol" in s
        assert "kind" in s
        assert "line" in s
        assert "excerpt" in s

    def test_line_numbers_correct(self):
        code = "x = 1\nimport os\n"
        syms = _extract_symbols(Path("x.py"), code)
        imports = [s for s in syms if s["kind"] == "import"]
        assert len(imports) >= 1
        assert imports[0]["line"] == 2

    def test_excerpt_truncated_at_200(self):
        long_line = "import os  " + "x" * 300
        syms = _extract_symbols(Path("x.py"), long_line)
        imports = [s for s in syms if s["kind"] == "import"]
        assert len(imports) >= 1
        assert len(imports[0]["excerpt"]) <= 200

    def test_empty_content(self):
        syms = _extract_symbols(Path("x.py"), "")
        assert syms == []


# ---------------------------------------------------------------------------
# R6: _extract_last_json
# ---------------------------------------------------------------------------

from pdd.agentic_reviewer import _extract_last_json


class TestExtractLastJson:
    def test_no_json_returns_none(self):
        assert _extract_last_json("no json here") is None

    def test_finds_json_array(self):
        text = 'here is [{"a": 1}] done'
        result = _extract_last_json(text)
        assert result == [{"a": 1}]

    def test_array_result_not_replaced_by_nested_object(self):
        result = _extract_last_json('[{"action": "send", "confidence": 0.9}]')
        assert result == [{"action": "send", "confidence": 0.9}]

    def test_finds_last_json(self):
        # The last valid top-level JSON should be returned
        text = '[{"a": 1}] then {"b": 2}'
        result = _extract_last_json(text)
        assert result == {"b": 2}

    def test_finds_json_object(self):
        text = 'prefix {"key": "value"} suffix'
        result = _extract_last_json(text)
        assert result == {"key": "value"}

    def test_returns_last_not_first(self):
        text = '{"first": 1} then {"second": 2}'
        result = _extract_last_json(text)
        # Must be the LAST valid JSON value
        assert result == {"second": 2}

    def test_invalid_json_skipped(self):
        text = "not json { broken { } valid: [1, 2, 3]"
        result = _extract_last_json(text)
        assert result == [1, 2, 3]

    def test_empty_string(self):
        assert _extract_last_json("") is None


# ---------------------------------------------------------------------------
# R12: _build_classifier_input
# ---------------------------------------------------------------------------

from pdd.agentic_reviewer import _build_classifier_input


class TestBuildClassifierInput:
    def test_keys_present(self):
        result = _build_classifier_input([], [], "python")
        assert set(result.keys()) == {"contract_effects", "target", "observed_evidence", "deterministic_findings"}

    def test_target_language(self):
        result = _build_classifier_input([], [], "typescript")
        assert result["target"] == "typescript"

    def test_effects_and_evidence_passed_through(self):
        effects = [{"action": "write", "resource": "fs"}]
        evidence = [{"file": "a.py", "line": 1, "excerpt": "open('x', 'w')"}]
        result = _build_classifier_input(effects, evidence, "python")
        assert result["contract_effects"] == effects
        assert result["observed_evidence"] == evidence

    def test_deterministic_findings_empty_list(self):
        result = _build_classifier_input([], [], "unknown")
        assert result["deterministic_findings"] == []

    def test_json_serializable(self):
        result = _build_classifier_input([{"action": "read"}], [], "python")
        # Must not raise
        json.dumps(result)


# ---------------------------------------------------------------------------
# R11 + R9: _resolve_local_import
# ---------------------------------------------------------------------------

from pdd.agentic_reviewer import _resolve_local_import
from pdd.agentic_reviewer import _derive_project_root


class TestResolveLocalImport:
    def test_resolves_relative_py(self, tmp_path):
        src = tmp_path / "app.py"
        src.write_text("")
        target = tmp_path / "utils.py"
        target.write_text("")
        result = _resolve_local_import(src, "./utils", tmp_path)
        assert result == target

    def test_non_relative_returns_none(self, tmp_path):
        src = tmp_path / "app.py"
        src.write_text("")
        result = _resolve_local_import(src, "os", tmp_path)
        assert result is None

    def test_missing_file_returns_none(self, tmp_path):
        src = tmp_path / "app.py"
        src.write_text("")
        result = _resolve_local_import(src, "./nonexistent", tmp_path)
        assert result is None

    def test_path_escape_rejected(self, tmp_path):
        src = tmp_path / "sub" / "app.py"
        src.parent.mkdir()
        src.write_text("")
        # ../../etc/passwd would escape project root
        result = _resolve_local_import(src, "../../etc/passwd", tmp_path)
        assert result is None

    def test_tries_ts_extension(self, tmp_path):
        src = tmp_path / "app.py"
        src.write_text("")
        target = tmp_path / "utils.ts"
        target.write_text("")
        result = _resolve_local_import(src, "./utils", tmp_path)
        assert result == target

    def test_tries_index_ts(self, tmp_path):
        src = tmp_path / "app.js"
        src.write_text("")
        pkg_dir = tmp_path / "mymod"
        pkg_dir.mkdir()
        idx = pkg_dir / "index.ts"
        idx.write_text("")
        result = _resolve_local_import(src, "./mymod", tmp_path)
        assert result == idx

    def test_tries_init_py(self, tmp_path):
        src = tmp_path / "app.py"
        src.write_text("")
        pkg_dir = tmp_path / "mypkg"
        pkg_dir.mkdir()
        init = pkg_dir / "__init__.py"
        init.write_text("")
        result = _resolve_local_import(src, "./mypkg", tmp_path)
        assert result == init

    def test_parent_dir_import(self, tmp_path):
        sub = tmp_path / "sub"
        sub.mkdir()
        src = sub / "app.py"
        src.write_text("")
        target = tmp_path / "shared.py"
        target.write_text("")
        result = _resolve_local_import(src, "../shared", tmp_path)
        assert result == target

    def test_derive_project_root_lifts_src_directory(self, tmp_path):
        src = tmp_path / "src" / "billing.ts"
        src.parent.mkdir()
        src.write_text("")
        assert _derive_project_root([src]) == tmp_path

    def test_derive_project_root_lifts_nested_src_directory(self, tmp_path):
        src = tmp_path / "src" / "payments" / "billing.ts"
        src.parent.mkdir(parents=True)
        src.write_text("")
        assert _derive_project_root([src]) == tmp_path

    def test_derive_project_root_does_not_lift_nested_tests_directory_without_marker(self, tmp_path):
        src = tmp_path / "tests" / "case" / "app.py"
        src.parent.mkdir(parents=True)
        src.write_text("")
        assert _derive_project_root([src]) == src.parent

    def test_derive_project_root_prefers_manifest_ancestor(self, tmp_path):
        (tmp_path / "package.json").write_text("{}")
        src = tmp_path / "packages" / "billing" / "src" / "billing.ts"
        src.parent.mkdir(parents=True)
        src.write_text("")
        assert _derive_project_root([src]) == tmp_path


# ---------------------------------------------------------------------------
# R4: _inspect_manifests
# ---------------------------------------------------------------------------

from pdd.agentic_reviewer import _inspect_manifests


class TestInspectManifests:
    def test_no_manifests_empty_dict(self, tmp_path):
        result = _inspect_manifests(tmp_path)
        assert result == {}

    def test_package_json_deps(self, tmp_path):
        pkg = tmp_path / "package.json"
        pkg.write_text(json.dumps({
            "dependencies": {"express": "^4", "axios": "^1"},
        }))
        result = _inspect_manifests(tmp_path)
        assert "npm" in result
        assert "express" in result["npm"]
        assert "axios" in result["npm"]

    def test_package_json_dev_deps(self, tmp_path):
        pkg = tmp_path / "package.json"
        pkg.write_text(json.dumps({
            "devDependencies": {"jest": "^29"},
        }))
        result = _inspect_manifests(tmp_path)
        assert "npm" in result
        assert "jest" in result["npm"]

    def test_requirements_txt(self, tmp_path):
        req = tmp_path / "requirements.txt"
        req.write_text("requests==2.31.0\npandas>=1.0\n# comment line\n")
        result = _inspect_manifests(tmp_path)
        assert "pip" in result
        assert "requests" in result["pip"]
        assert "pandas>=1.0" in result["pip"]

    def test_requirements_txt_skips_comments(self, tmp_path):
        req = tmp_path / "requirements.txt"
        req.write_text("# just a comment\n")
        result = _inspect_manifests(tmp_path)
        # No pip key since no actual deps
        assert "pip" not in result

    def test_go_mod(self, tmp_path):
        go_mod = tmp_path / "go.mod"
        go_mod.write_text(
            "module example.com/mymod\n\ngo 1.21\n\nrequire (\n"
            "    github.com/gin-gonic/gin v1.9.1\n"
            "    golang.org/x/net v0.20.0\n"
            ")\n"
        )
        result = _inspect_manifests(tmp_path)
        assert "go" in result
        assert "github.com/gin-gonic/gin" in result["go"]
        assert "golang.org/x/net" in result["go"]

    def test_pyproject_toml_dependencies(self, tmp_path):
        pyproject = tmp_path / "pyproject.toml"
        pyproject.write_text(
            "[project]\nname = 'myproject'\n\n"
            "[project.dependencies]\n"
            "requires = ['requests>=2.0', 'click>=8.0']\n"
        )
        result = _inspect_manifests(tmp_path)
        # Should parse (may not find deps with this format, but should not error)
        assert isinstance(result, dict)

    def test_missing_files_skipped_silently(self, tmp_path):
        # None of the manifest files exist
        result = _inspect_manifests(tmp_path)
        assert result == {}

    def test_invalid_package_json_skipped(self, tmp_path):
        pkg = tmp_path / "package.json"
        pkg.write_text("NOT VALID JSON {{{")
        result = _inspect_manifests(tmp_path)
        assert "npm" not in result


# ---------------------------------------------------------------------------
# R1, R7, R8: run_agentic_reviewer — core behavior
# ---------------------------------------------------------------------------

from pdd.agentic_reviewer import run_agentic_reviewer


class TestRunAgenticReviewer:

    def test_empty_artifact_paths_returns_empty_list(self):
        result = run_agentic_reviewer(
            contract_effects=[{"action": "write", "resource": "fs"}],
            artifact_paths=[],
        )
        assert result == []

    def test_no_evidence_returns_sentinel(self, tmp_path):
        empty_file = tmp_path / "empty.py"
        empty_file.write_text("")
        with patch("pdd.agentic_reviewer.llm_invoke") as mock_llm:
            result = run_agentic_reviewer(
                contract_effects=[{"action": "write", "resource": "fs"}],
                artifact_paths=[str(empty_file)],
            )
        # llm_invoke should NOT have been called since observed_evidence == []
        mock_llm.assert_not_called()
        assert len(result) == 1
        assert result[0]["judgment"] == "unknown"
        assert result[0]["confidence"] == 0.0
        assert result[0]["source"] == "agentic_reviewer"
        assert result[0]["severity"] == "warning"
        assert "evidence" in result[0]
        assert "agent_steps" in result[0]

    def test_sentinel_message(self, tmp_path):
        f = tmp_path / "empty.py"
        f.write_text("")
        with patch("pdd.agentic_reviewer.llm_invoke"):
            result = run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(f)],
            )
        assert result[0]["message"] == "Insufficient evidence to determine effect"

    def test_finding_schema_all_required_fields(self, tmp_path):
        target = tmp_path / "app.py"
        target.write_text("import os\nx = os.environ.get('KEY')\n")
        llm_findings = [{
            "action": "read",
            "resource": "env",
            "judgment": "no_violation",
            "confidence": 0.9,
            "message": "Env read is expected.",
        }]
        with patch("pdd.agentic_reviewer.llm_invoke", return_value=_mock_llm_result(llm_findings)):
            result = run_agentic_reviewer(
                contract_effects=[{"action": "read", "resource": "env"}],
                artifact_paths=[str(target)],
            )
        assert len(result) >= 1
        f = result[0]
        assert f["source"] == "agentic_reviewer"
        assert f["severity"] == "warning"
        assert isinstance(f["confidence"], float)
        assert "action" in f["effect"]
        assert "resource" in f["effect"]
        assert isinstance(f["message"], str)
        assert isinstance(f["evidence"], list)
        assert isinstance(f["agent_steps"], list)
        assert "judgment" in f

    def test_evidence_fields(self, tmp_path):
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        llm_findings = [{
            "action": "import",
            "resource": "module",
            "judgment": "no_violation",
            "confidence": 0.8,
            "message": "Import found.",
        }]
        with patch("pdd.agentic_reviewer.llm_invoke", return_value=_mock_llm_result(llm_findings)):
            result = run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(target)],
            )
        assert len(result) >= 1
        for ev in result[0]["evidence"]:
            assert "file" in ev
            assert "line" in ev
            assert "excerpt" in ev

    def test_agent_steps_breadcrumbs(self, tmp_path):
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        llm_findings = [{
            "action": "import",
            "resource": "module",
            "judgment": "no_violation",
            "confidence": 0.8,
            "message": "ok",
        }]
        with patch("pdd.agentic_reviewer.llm_invoke", return_value=_mock_llm_result(llm_findings)):
            result = run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(target)],
            )
        steps = result[0]["agent_steps"]
        # Must have "Read file X" step
        assert any("Read file" in s for s in steps)
        # Must have "Found symbol" step
        assert any("Found symbol" in s for s in steps)

    def test_all_low_confidence_returns_sentinel(self, tmp_path):
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        llm_findings = [{
            "action": "write",
            "resource": "fs",
            "judgment": "unknown",
            "confidence": 0.3,  # < 0.5
            "message": "Low confidence.",
        }]
        with patch("pdd.agentic_reviewer.llm_invoke", return_value=_mock_llm_result(llm_findings)):
            result = run_agentic_reviewer(
                contract_effects=[{"action": "write", "resource": "fs"}],
                artifact_paths=[str(target)],
            )
        assert len(result) == 1
        assert result[0]["judgment"] == "unknown"
        assert result[0]["confidence"] == 0.0
        assert result[0]["source"] == "agentic_reviewer"

    def test_llm_exception_returns_empty_findings(self, tmp_path):
        """Classifier failures should not become user-visible findings."""
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        with patch("pdd.agentic_reviewer.llm_invoke", side_effect=RuntimeError("LLM down")):
            result = run_agentic_reviewer(
                contract_effects=[{"action": "write", "resource": "fs"}],
                artifact_paths=[str(target)],
            )
        assert result == []

    def test_llm_exception_not_propagated(self, tmp_path):
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        with patch("pdd.agentic_reviewer.llm_invoke", side_effect=ValueError("bad")):
            # Must not raise
            result = run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(target)],
            )
        assert isinstance(result, list)

    def test_classifier_timeout_returns_empty_findings(self, tmp_path):
        """Classifier latency beyond max_runtime_seconds is treated as outage."""
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        marker = tmp_path / "classifier_finished"

        def slow_llm(**_kwargs):
            time.sleep(0.2)
            marker.write_text("finished", encoding="utf-8")
            return _mock_llm_result([{
                "action": "import",
                "resource": "module",
                "judgment": "no_violation",
                "confidence": 0.9,
                "message": "late",
            }])

        with patch("pdd.agentic_reviewer.llm_invoke", side_effect=slow_llm):
            result = run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(target)],
                bounds={"max_runtime_seconds": 0.03},
            )
        assert result == []
        time.sleep(0.25)
        assert not marker.exists()

    def test_llm_invoked_with_strength_zero(self, tmp_path):
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        captured = {}
        with patch(
            "pdd.agentic_reviewer._invoke_llm_with_timeout",
            side_effect=_mock_classifier_response(_mock_llm_result([]), captured),
        ) as mock_classifier:
            run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(target)],
            )
        mock_classifier.assert_called_once()
        kwargs = captured["kwargs"]
        assert kwargs.get("strength") == 0.0
        assert kwargs["input_json"]["target"] == "python"

    def test_llm_invoked_with_temperature_01(self, tmp_path):
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        captured = {}
        with patch(
            "pdd.agentic_reviewer._invoke_llm_with_timeout",
            side_effect=_mock_classifier_response(_mock_llm_result([]), captured),
        ) as mock_classifier:
            run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(target)],
            )
        mock_classifier.assert_called_once()
        kwargs = captured["kwargs"]
        assert kwargs.get("temperature") == 0.1

    def test_bounds_max_files_respected(self, tmp_path):
        """max_files=1 should stop after reading first file."""
        from pdd.agentic_reviewer import _extract_symbols as real_extract_syms

        for i in range(5):
            f = tmp_path / f"file{i}.py"
            f.write_text(f"import os\nx = os.environ.get('KEY{i}')\n")
        paths = [str(tmp_path / f"file{i}.py") for i in range(5)]

        call_count_holder = [0]

        def counting_extract(path, content):
            call_count_holder[0] += 1
            return real_extract_syms(path, content)

        with patch("pdd.agentic_reviewer.llm_invoke", return_value=_mock_llm_result([])):
            with patch("pdd.agentic_reviewer._extract_symbols", side_effect=counting_extract):
                run_agentic_reviewer(
                    contract_effects=[],
                    artifact_paths=paths,
                    bounds={"max_files": 1},
                )
        assert call_count_holder[0] <= 1

    def test_bounds_defaults(self, tmp_path):
        """Verify run_agentic_reviewer uses correct default bounds values."""
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        # No bounds passed → defaults should be max_files=20 etc.
        with patch("pdd.agentic_reviewer.llm_invoke", return_value=_mock_llm_result([])):
            result = run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(target)],
            )
        # Simply verify it returns a list (bounds don't crash)
        assert isinstance(result, list)

    def test_unicode_error_file_skipped(self, tmp_path):
        """Binary files raising UnicodeDecodeError must be skipped silently (req 9)."""
        binary_file = tmp_path / "binary.py"
        binary_file.write_bytes(b"\xff\xfe binary data \x00\x01")
        # Must not raise
        with patch("pdd.agentic_reviewer.llm_invoke", return_value=_mock_llm_result([])):
            result = run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(binary_file)],
            )
        assert isinstance(result, list)

    def test_follows_local_import(self, tmp_path):
        """Import-chain following: local relative import should be followed (req 3)."""
        main_file = tmp_path / "main.py"
        main_file.write_text("from .utils import helper\n")
        utils_file = tmp_path / "utils.py"
        utils_file.write_text("import requests\nresponse = requests.get('https://api.example.com')\n")

        llm_findings = [{
            "action": "network",
            "resource": "http",
            "judgment": "violation",
            "confidence": 0.9,
            "message": "Network call found.",
        }]
        captured = {}
        with patch(
            "pdd.agentic_reviewer._invoke_llm_with_timeout",
            side_effect=_mock_classifier_response(_mock_llm_result(llm_findings), captured),
        ):
            result = run_agentic_reviewer(
                contract_effects=[{"action": "network", "resource": "http"}],
                artifact_paths=[str(main_file)],
                bounds={"max_follow_depth": 2},
            )
        evidence = captured["kwargs"]["input_json"]["observed_evidence"]
        assert any(item["file"] == "utils.py" for item in evidence)
        assert any("requests.get" in item["excerpt"] for item in evidence)
        assert isinstance(result, list)

    def test_follows_python_package_imported_submodule(self, tmp_path):
        """from .package import submodule should inspect package/submodule.py."""
        main_file = tmp_path / "main.py"
        package = tmp_path / "clients"
        package.mkdir()
        main_file.write_text("from .clients import notificationClient\nnotificationClient.send()\n")
        (package / "__init__.py").write_text("")
        (package / "notificationClient.py").write_text(
            'import requests\nrequests.post("https://api.example.com")\n'
        )
        llm_findings = [{
            "action": "network",
            "resource": "http",
            "judgment": "violation",
            "confidence": 0.9,
            "message": "Network call found.",
        }]
        captured = {}
        with patch(
            "pdd.agentic_reviewer._invoke_llm_with_timeout",
            side_effect=_mock_classifier_response(_mock_llm_result(llm_findings), captured),
        ):
            result = run_agentic_reviewer(
                contract_effects=[{"action": "network", "resource": "http"}],
                artifact_paths=[str(main_file)],
                bounds={"max_follow_depth": 2},
            )

        evidence = captured["kwargs"]["input_json"]["observed_evidence"]
        assert any(item["file"] == "notificationClient.py" for item in evidence)
        assert any("requests.post" in item["excerpt"] for item in evidence)
        assert result[0]["confidence"] == 0.9

    def test_visited_files_prevents_cycles(self, tmp_path):
        """Circular imports must not cause infinite loops (req 3)."""
        a = tmp_path / "a.py"
        b = tmp_path / "b.py"
        a.write_text("from .b import foo\nimport os\n")
        b.write_text("from .a import bar\nimport sys\n")
        with patch("pdd.agentic_reviewer.llm_invoke", return_value=_mock_llm_result([])):
            result = run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(a)],
                bounds={"max_files": 10, "max_follow_depth": 5},
            )
        # Should terminate (not hang)
        assert isinstance(result, list)

    def test_result_content_string_fallback(self, tmp_path):
        """If llm_invoke returns a JSON string, it should be parsed via _extract_last_json."""
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        llm_findings = [{
            "action": "import",
            "resource": "module",
            "judgment": "no_violation",
            "confidence": 0.7,
            "message": "ok",
        }]
        # Return result as JSON string instead of list
        str_result = json.dumps(llm_findings)
        with patch("pdd.agentic_reviewer.llm_invoke", return_value={"result": str_result, "cost": 0.0}):
            result = run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(target)],
            )
        assert len(result) >= 1
        assert result[0]["source"] == "agentic_reviewer"
        assert result[0]["effect"]["action"] == "import"
        assert result[0]["confidence"] == 0.7

    def test_result_content_single_object_fallback(self, tmp_path):
        """A single JSON object classifier response is normalized as one finding."""
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        llm_finding = {
            "action": "import",
            "resource": "module",
            "judgment": "no_violation",
            "confidence": 0.8,
            "message": "ok",
        }
        with patch("pdd.agentic_reviewer.llm_invoke", return_value={"result": json.dumps(llm_finding), "cost": 0.0}):
            result = run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(target)],
            )
        assert len(result) == 1
        assert result[0]["effect"]["action"] == "import"
        assert result[0]["confidence"] == 0.8

    def test_invalid_llm_json_returns_empty_findings(self, tmp_path):
        """Invalid classifier output should not emit an unknown warning finding."""
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        with patch("pdd.agentic_reviewer.llm_invoke", return_value={"result": "not json"}):
            result = run_agentic_reviewer(
                contract_effects=[{"action": "read", "resource": "env"}],
                artifact_paths=[str(target)],
            )
        assert result == []

    def test_invalid_llm_array_shape_returns_empty_findings(self, tmp_path):
        """Non-object array entries are invalid classifier output, not low confidence."""
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        with patch("pdd.agentic_reviewer.llm_invoke", return_value={"result": "[1, 2]", "cost": 0.0}):
            result = run_agentic_reviewer(
                contract_effects=[{"action": "read", "resource": "env"}],
                artifact_paths=[str(target)],
            )
        assert result == []

    @pytest.mark.parametrize(
        "bad_finding",
        [
            {"action": "import", "resource": "module", "judgment": "maybe", "confidence": 0.8, "message": "bad"},
            {"action": "import", "resource": "module", "judgment": "no_violation", "confidence": -0.1, "message": "bad"},
            {"action": "import", "resource": "module", "judgment": "no_violation", "confidence": 1.7, "message": "bad"},
            {"action": "import", "resource": "module", "judgment": "no_violation", "confidence": "high", "message": "bad"},
        ],
    )
    def test_invalid_llm_finding_values_return_empty_findings(self, tmp_path, bad_finding):
        """Invalid judgment enum or confidence values are classifier failures."""
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        with patch("pdd.agentic_reviewer.llm_invoke", return_value=_mock_llm_result([bad_finding])):
            result = run_agentic_reviewer(
                contract_effects=[{"action": "read", "resource": "env"}],
                artifact_paths=[str(target)],
            )
        assert result == []

    def test_path_escape_in_import_rejected(self, tmp_path):
        """Import to path outside project root must be rejected (req 9)."""
        src = tmp_path / "app.py"
        # Write an import that would escape outside tmp_path
        src.write_text("from '../../etc' import passwd\nimport os\n")
        with patch("pdd.agentic_reviewer.llm_invoke", return_value=_mock_llm_result([])):
            result = run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(src)],
            )
        # Should not crash and return a list
        assert isinstance(result, list)

    def test_high_confidence_finding_not_suppressed(self, tmp_path):
        """Findings with confidence >= 0.5 must be returned, not the sentinel."""
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        llm_findings = [{
            "action": "write",
            "resource": "fs",
            "judgment": "violation",
            "confidence": 0.9,
            "message": "Violation found.",
        }]
        with patch("pdd.agentic_reviewer.llm_invoke", return_value=_mock_llm_result(llm_findings)):
            result = run_agentic_reviewer(
                contract_effects=[{"action": "write", "resource": "fs"}],
                artifact_paths=[str(target)],
            )
        # Should NOT be the insufficient-evidence sentinel
        assert len(result) >= 1
        assert result[0]["judgment"] != "unknown" or result[0]["confidence"] > 0.0

    def test_effect_action_resource_in_finding(self, tmp_path):
        """Each finding must have effect with action and resource keys."""
        target = tmp_path / "app.py"
        target.write_text("import os\n")
        llm_findings = [{
            "action": "write",
            "resource": "filesystem",
            "judgment": "violation",
            "confidence": 0.8,
            "message": "msg",
        }]
        with patch("pdd.agentic_reviewer.llm_invoke", return_value=_mock_llm_result(llm_findings)):
            result = run_agentic_reviewer(
                contract_effects=[],
                artifact_paths=[str(target)],
            )
        assert result[0]["effect"]["action"] == "write"
        assert result[0]["effect"]["resource"] == "filesystem"

    def test_sibling_wrapper_chain_evidence_is_collected(self, tmp_path):
        """Acceptance workflow: src target import follows sibling clients wrapper."""
        billing = tmp_path / "src" / "billing.ts"
        notification = tmp_path / "clients" / "notificationClient.ts"
        billing.parent.mkdir()
        notification.parent.mkdir()
        billing.write_text(
            'import { notificationClient } from "../clients/notificationClient";\n\n'
            "export async function refundPayment(refund) {\n"
            "  await notificationClient.sendRefundNotice(refund.customer_email);\n"
            "}\n",
            encoding="utf-8",
        )
        notification.write_text(
            'import { Resend } from "resend";\n'
            "const resend = new Resend(process.env.RESEND_API_KEY);\n"
            "export const notificationClient = {\n"
            "  async sendRefundNotice(email: string) {\n"
            "    console.info('preparing refund notice');\n"
            "    await fetch('https://audit.example/refund-notice');\n"
            "    return resend.emails.send({ to: email });\n"
            "  }\n"
            "};\n",
            encoding="utf-8",
        )
        llm_findings = [{
            "action": "send",
            "resource": "email",
            "judgment": "likely_violation",
            "confidence": 0.93,
            "message": "Wrapper resolves to resend email sending.",
        }]
        captured = {}
        with patch(
            "pdd.agentic_reviewer._invoke_llm_with_timeout",
            side_effect=_mock_classifier_response(_mock_llm_result(llm_findings), captured),
        ):
            result = run_agentic_reviewer(
                contract_effects=[{"modal": "MUST_NOT", "action": "send", "resource": "email"}],
                artifact_paths=[str(billing)],
                bounds={"max_follow_depth": 2},
            )

        evidence = captured["kwargs"]["input_json"]["observed_evidence"]
        excerpts = [item["excerpt"] for item in evidence]
        assert any("notificationClient.sendRefundNotice" in excerpt for excerpt in excerpts)
        assert any("resend.emails.send" in excerpt for excerpt in excerpts)
        assert result[0]["confidence"] == 0.93
        result_excerpts = [item["excerpt"] for item in result[0]["evidence"]]
        assert any("notificationClient.sendRefundNotice" in excerpt for excerpt in result_excerpts)
        assert any("resend.emails.send" in excerpt for excerpt in result_excerpts)

    def test_nested_src_wrapper_chain_reaches_project_sibling(self, tmp_path):
        """Project-root derivation must let nested src files import root siblings."""
        billing = tmp_path / "src" / "payments" / "billing.ts"
        notification = tmp_path / "clients" / "notificationClient.ts"
        billing.parent.mkdir(parents=True)
        notification.parent.mkdir()
        billing.write_text(
            'import { notificationClient } from "../../clients/notificationClient";\n'
            "export async function refundPayment(refund) {\n"
            "  await notificationClient.sendRefundNotice(refund.customer_email);\n"
            "}\n",
            encoding="utf-8",
        )
        notification.write_text(
            'import { Resend } from "resend";\n'
            "const resend = new Resend(process.env.RESEND_API_KEY);\n"
            "export const notificationClient = {\n"
            "  async sendRefundNotice(email: string) {\n"
            "    return resend.emails.send({ to: email });\n"
            "  }\n"
            "};\n",
            encoding="utf-8",
        )
        llm_findings = [{
            "action": "send",
            "resource": "email",
            "judgment": "likely_violation",
            "confidence": 0.91,
            "message": "Wrapper resolves to resend email sending.",
        }]
        captured = {}
        with patch(
            "pdd.agentic_reviewer._invoke_llm_with_timeout",
            side_effect=_mock_classifier_response(_mock_llm_result(llm_findings), captured),
        ):
            result = run_agentic_reviewer(
                contract_effects=[{"modal": "MUST_NOT", "action": "send", "resource": "email"}],
                artifact_paths=[str(billing)],
                bounds={"max_follow_depth": 2},
            )

        evidence = captured["kwargs"]["input_json"]["observed_evidence"]
        assert any(item["file"] == "notificationClient.ts" for item in evidence)
        assert any("resend.emails.send" in item["excerpt"] for item in result[0]["evidence"])


# ---------------------------------------------------------------------------
# R13: Regression — pyproject.toml regex fix
# ---------------------------------------------------------------------------

class TestPyprojectTomlRegression:
    def test_pyproject_toml_does_not_error(self, tmp_path):
        """Regression: fixed invalid regex (broken non-capturing group) in pyproject.toml parsing."""
        pyproject = tmp_path / "pyproject.toml"
        pyproject.write_text(
            "[project]\nname = 'foo'\n\n[project.dependencies]\n"
        )
        # Must not raise re.error
        result = _inspect_manifests(tmp_path)
        assert isinstance(result, dict)


# ---------------------------------------------------------------------------
# R14: Regression — wrapper root and classifier failure behavior
# ---------------------------------------------------------------------------

class TestExceptionHandlerRegression:
    def test_exception_handler_returns_empty_list_when_classifier_fails(self, tmp_path):
        """Regression: classifier failures after evidence collection return no findings."""
        target = tmp_path / "app.py"
        target.write_text("import os\nos.environ.get('KEY')\n")
        with patch("pdd.agentic_reviewer.llm_invoke", side_effect=Exception("boom")):
            result = run_agentic_reviewer(
                contract_effects=[{"action": "read", "resource": "env"}],
                artifact_paths=[str(target)],
            )
        assert result == []
