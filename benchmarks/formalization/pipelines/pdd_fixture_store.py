"""Store and replay ``pdd generate`` / ``pdd test`` artifacts for CI-safe M2 runs."""
from __future__ import annotations

import hashlib
import json
import shutil
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

FIXTURE_MANIFEST = "fixture_manifest.json"
GENERATED = "generated"
SRC = "src"
TESTS = "tests"


def fixture_arm_dir(fixtures_root: Path, arm: str) -> Path:
    """Return ``<fixtures_root>/<arm>/generated/{src,tests}`` parent."""
    return fixtures_root / arm / GENERATED


def fixture_code_path(fixtures_root: Path, arm: str, module: str) -> Path:
    return fixture_arm_dir(fixtures_root, arm) / SRC / f"{module}.py"


def fixture_test_path(fixtures_root: Path, arm: str, module: str) -> Path:
    return fixture_arm_dir(fixtures_root, arm) / TESTS / f"test_{module}.py"


def arm_has_fixtures(fixtures_root: Path, arm: str, module: str) -> bool:
    """True when both code and test fixtures exist for an arm."""
    return (
        fixture_code_path(fixtures_root, arm, module).is_file()
        and fixture_test_path(fixtures_root, arm, module).is_file()
    )


def copy_arm_fixtures(
    *,
    fixtures_root: Path,
    arm: str,
    module: str,
    work_dir: Path,
) -> dict[str, Any]:
    """Copy recorded fixtures into a generation work dir."""
    src_dir = work_dir / GENERATED / SRC
    tests_dir = work_dir / GENERATED / TESTS
    src_dir.mkdir(parents=True, exist_ok=True)
    tests_dir.mkdir(parents=True, exist_ok=True)

    code_src = fixture_code_path(fixtures_root, arm, module)
    test_src = fixture_test_path(fixtures_root, arm, module)
    code_dst = src_dir / f"{module}.py"
    test_dst = tests_dir / f"test_{module}.py"
    shutil.copy2(code_src, code_dst)
    shutil.copy2(test_src, test_dst)

    manifest_path = fixtures_root / FIXTURE_MANIFEST
    meta: dict[str, Any] = {}
    if manifest_path.is_file():
        meta = json.loads(manifest_path.read_text(encoding="utf-8"))

    return {
        "stage": "pdd_fixture_replay",
        "arm": arm,
        "fixtures_root": str(fixtures_root),
        "code_path": str(code_dst),
        "test_path": str(test_dst),
        "fixture_manifest": meta,
        "code_source": "pdd_fixtures",
        "test_source": "pdd_fixtures",
    }


def save_arm_fixtures(
    *,
    fixtures_root: Path,
    arm: str,
    module: str,
    work_dir: Path,
    prompt_path: Path,
    provenance: str,
    extra: Optional[dict[str, Any]] = None,
) -> None:
    """Persist generated code/tests from a live M2 arm run."""
    src = work_dir / GENERATED / SRC / f"{module}.py"
    tests = work_dir / GENERATED / TESTS / f"test_{module}.py"
    if not src.is_file() or not tests.is_file():
        raise FileNotFoundError(
            f"Missing generated artifacts for {arm}: {src} or {tests}"
        )

    dst_code = fixture_code_path(fixtures_root, arm, module)
    dst_test = fixture_test_path(fixtures_root, arm, module)
    dst_code.parent.mkdir(parents=True, exist_ok=True)
    dst_test.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst_code)
    shutil.copy2(tests, dst_test)

    manifest_path = fixtures_root / FIXTURE_MANIFEST
    manifest: dict[str, Any] = {}
    if manifest_path.is_file():
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest.setdefault("arms", {})
    manifest["updated_at"] = datetime.now(timezone.utc).isoformat()
    manifest["provenance"] = provenance
    manifest["arms"][arm] = {
        "prompt": str(prompt_path),
        "prompt_sha256": _sha256(prompt_path),
        "module": module,
        "code": str(dst_code.relative_to(fixtures_root)),
        "tests": str(dst_test.relative_to(fixtures_root)),
        **(extra or {}),
    }
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")


def save_recorded_a1(*, fixtures_root: Path, arm: str, prompt_path: Path) -> Path:
    """Copy a generated A1.prompt into the fixture tree for CI replay."""
    if arm != "A1":
        raise ValueError("save_recorded_a1 only supports arm A1")
    dst = fixtures_root / "A1.prompt"
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(prompt_path, dst)
    manifest_path = fixtures_root / FIXTURE_MANIFEST
    manifest: dict[str, Any] = {}
    if manifest_path.is_file():
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["a1_prompt"] = str(dst.relative_to(fixtures_root))
    manifest["a1_recorded_at"] = datetime.now(timezone.utc).isoformat()
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return dst


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()
