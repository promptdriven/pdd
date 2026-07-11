"""Post-command freshness property tests for issue #1926."""

from __future__ import annotations

import ast
from pathlib import Path

import pytest

import pdd.sync_determine_operation as sync_state
from pdd.fingerprint_transaction import FingerprintTransaction


MUTATING_OPERATIONS = (
    "sync",
    "generate",
    "example",
    "update",
    "fix",
    "auto-deps",
    "ci-heal",
)


@pytest.mark.parametrize("operation", MUTATING_OPERATIONS)
def test_successful_mutation_is_immediately_fresh(
    operation: str,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Every supported mutator must converge after its transaction commits."""

    (tmp_path / ".pddrc").write_text("{}", encoding="utf-8")
    paths = {
        "prompt": tmp_path / "prompts" / "widget_python.prompt",
        "code": tmp_path / "src" / "widget.py",
        "example": tmp_path / "examples" / "widget_example.py",
        "test": tmp_path / "tests" / "test_widget.py",
    }
    for key, path in paths.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"{operation}: {key}\n", encoding="utf-8")

    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sync_state, "get_pdd_file_paths", lambda *args, **kwargs: paths)

    with FingerprintTransaction("widget", "python", operation, paths=paths):
        pass

    decision = sync_state.sync_determine_operation(
        "widget",
        "python",
        target_coverage=90.0,
        log_mode=True,
        skip_tests=True,
        skip_verify=True,
    )
    if operation == "auto-deps":
        # Auto-deps intentionally schedules generation before declaring the
        # workflow complete. Prove that the required follow-up also converges.
        assert decision.operation == "generate", decision.reason
        with FingerprintTransaction("widget", "python", "generate", paths=paths):
            pass
        decision = sync_state.sync_determine_operation(
            "widget",
            "python",
            target_coverage=90.0,
            log_mode=True,
            skip_tests=True,
            skip_verify=True,
        )
    assert decision.operation == "nothing", decision.reason


def test_all_production_finalizers_route_through_transaction() -> None:
    """Static guard: new command-specific fingerprint writers are forbidden."""

    repo_root = Path(__file__).resolve().parents[1]
    required_modules = {
        "pdd/operation_log.py": "save_fingerprint",
        "pdd/sync_orchestration.py": "_save_fingerprint_atomic",
        "pdd/sync_main.py": "sync_main",
        "pdd/auto_deps_main.py": "auto_deps_main",
        "pdd/metadata_sync.py": "run_metadata_sync",
        "pdd/ci_drift_heal.py": "_run_metadata_sync_safe",
        "pdd/update_main.py": "_finalize_single_file_fingerprint",
        "pdd/pin_example_hack.py": "_save_operation_fingerprint",
    }

    for relative_path, function_name in required_modules.items():
        tree = ast.parse((repo_root / relative_path).read_text(encoding="utf-8"))
        function = next(
            node
            for node in ast.walk(tree)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.name == function_name
        )
        referenced_names = {
            node.id for node in ast.walk(function) if isinstance(node, ast.Name)
        }
        assert "FingerprintTransaction" in referenced_names, (
            f"{relative_path}:{function_name} bypasses FingerprintTransaction"
        )


def test_only_transaction_module_performs_direct_fingerprint_json_write() -> None:
    """No top-level PDD module may reintroduce the legacy JSON writer."""
    repo_root = Path(__file__).resolve().parents[1]
    transaction_source = (repo_root / "pdd/fingerprint_transaction.py").read_text(
        encoding="utf-8"
    )
    assert "os.replace" in transaction_source

    for path in (repo_root / "pdd").glob("*.py"):
        if path.name in {"fingerprint_transaction.py", "sync_orchestration.py"}:
            continue
        source = path.read_text(encoding="utf-8")
        assert "json.dump(asdict(fingerprint)" not in source, path
