"""Regeneration stability checks for PDD dev units (``pdd checkup drift``)."""
from __future__ import annotations

import ast
import hashlib
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

from .evidence_store import ManifestView, resolve_prompt_path
try:
    from .gate_main import run_gate_policy
except ModuleNotFoundError:  # pragma: no cover - optional in minimal installs
    def run_gate_policy(*_args, **_kwargs):
        class _Result:
            passed = True

        return _Result()

_PASS_TOKENS = {"pass", "passed", "ok", "success", "clean", "not_applicable"}


@dataclass
class RunSnapshot:
    run_index: int
    code_sha256: str
    public_api: list[str]
    tests_passed: bool
    stories_passed: bool
    verify_passed: bool
    policy_passed: bool

    def as_dict(self) -> dict[str, Any]:
        return {
            "run_index": self.run_index,
            "code_sha256": self.code_sha256,
            "public_api": self.public_api,
            "tests_passed": self.tests_passed,
            "stories_passed": self.stories_passed,
            "verify_passed": self.verify_passed,
            "policy_passed": self.policy_passed,
        }


@dataclass
class DriftReport:
    devunit: str
    prompt_path: str
    code_path: str
    runs: int
    snapshots: list[RunSnapshot] = field(default_factory=list)
    public_api_unchanged: bool = True
    implementation_changed: bool = False
    behavior_unchanged: bool = True
    status: str = "stable"
    dry_run: bool = False

    @property
    def passed(self) -> bool:
        return self.status == "stable"

    @property
    def exit_code(self) -> int:
        return 0 if self.passed else 1

    def as_dict(self) -> dict[str, Any]:
        tests_passed = sum(1 for snap in self.snapshots if snap.tests_passed)
        stories_passed = sum(1 for snap in self.snapshots if snap.stories_passed)
        verify_passed = sum(1 for snap in self.snapshots if snap.verify_passed)
        policy_passed = sum(1 for snap in self.snapshots if snap.policy_passed)
        return {
            "devunit": self.devunit,
            "prompt_path": self.prompt_path,
            "code_path": self.code_path,
            "runs": self.runs,
            "dry_run": self.dry_run,
            "status": self.status,
            "public_api_unchanged": self.public_api_unchanged,
            "implementation_changed": self.implementation_changed,
            "behavior_unchanged": self.behavior_unchanged,
            "tests": f"passed {tests_passed}/{self.runs}",
            "stories": f"passed {stories_passed}/{self.runs}",
            "verify": f"passed {verify_passed}/{self.runs}",
            "policy": f"passed {policy_passed}/{self.runs}",
            "snapshots": [snap.as_dict() for snap in self.snapshots],
        }


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _public_api(path: Path) -> list[str]:
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"))
    except (OSError, SyntaxError):
        return []
    names: list[str] = []
    for node in tree.body:
        if isinstance(node, ast.FunctionDef):
            names.append(f"def {node.name}")
        elif isinstance(node, ast.AsyncFunctionDef):
            names.append(f"async def {node.name}")
        elif isinstance(node, ast.ClassDef):
            names.append(f"class {node.name}")
    return sorted(names)


def _resolve_code_path(prompt_path: Path, project_root: Path) -> Path:
    stem = prompt_path.stem.replace("_python", "").replace("_typescript", "")
    candidates = [
        project_root / "pdd" / f"{stem}.py",
        project_root / "src" / f"{stem}.py",
        project_root / f"{stem}.py",
    ]
    for candidate in candidates:
        if candidate.is_file():
            return candidate.resolve()
    raise FileNotFoundError(
        f"Could not locate generated code for {prompt_path.name}; pass --code-file"
    )


def _path_score(path: Path, *, expected_stem: str, devunit: str) -> int:
    score = 0
    if path.is_file():
        score += 100
    if path.suffix == ".py":
        score += 40
    if path.stem == expected_stem:
        score += 30
    if devunit in path.stem:
        score += 20
    if "/pdd/" in path.as_posix():
        score += 10
    return score


def _select_manifest_output(
    manifest: ManifestView,
    *,
    project_root: Path,
    expected_stem: str,
    devunit: str,
) -> Optional[Path]:
    best: Optional[Path] = None
    best_score = -1
    for output in manifest.outputs:
        raw = output.get("path")
        if not raw:
            continue
        candidate = Path(raw)
        if not candidate.is_absolute():
            candidate = project_root / candidate
        score = _path_score(candidate, expected_stem=expected_stem, devunit=devunit)
        if score > best_score:
            best_score = score
            best = candidate
    if best is not None and best.is_file():
        return best.resolve()
    return None


def _load_manifest_paths(
    devunit: str,
    project_root: Path,
    from_evidence: Optional[Path],
) -> tuple[Path, Path, Optional[ManifestView]]:
    if from_evidence is None:
        latest = project_root / ".pdd" / "evidence" / "devunits" / f"{devunit}.latest.json"
        if latest.is_file():
            from_evidence = latest
    if from_evidence is None or not from_evidence.is_file():
        prompt = resolve_prompt_path(project_root, devunit)
        if prompt is None:
            raise FileNotFoundError(f"Could not resolve prompt for dev unit {devunit!r}")
        return prompt, _resolve_code_path(prompt, project_root), None

    manifest = ManifestView.from_file(from_evidence.resolve(), project_root)
    prompt = manifest.prompt_path or resolve_prompt_path(project_root, devunit, manifest.raw)
    if prompt is None:
        raise FileNotFoundError(f"Evidence manifest missing prompt path: {from_evidence}")

    expected_stem = prompt.stem.replace("_python", "").replace("_typescript", "")
    picked = _select_manifest_output(
        manifest,
        project_root=project_root,
        expected_stem=expected_stem,
        devunit=devunit,
    )
    if picked is not None:
        return prompt, picked, manifest
    return prompt, _resolve_code_path(prompt, project_root), manifest


def _run_pytest(tests: list[Path], project_root: Path) -> bool:
    if not tests:
        return True
    cmd = [sys.executable, "-m", "pytest", "-q", *[str(path) for path in tests]]
    completed = subprocess.run(
        cmd,
        cwd=project_root,
        capture_output=True,
        text=True,
        check=False,
    )
    return completed.returncode == 0


def _discover_tests(code_path: Path, project_root: Path) -> list[Path]:
    module = code_path.stem
    candidates = [
        project_root / "tests" / f"test_{module}.py",
        project_root / "tests" / f"test_{module.replace('_python', '')}.py",
    ]
    return [path for path in candidates if path.is_file()]


def _regenerate_code(
    prompt_path: Path,
    code_path: Path,
    *,
    model: Optional[str],
    project_root: Path,
) -> None:
    cmd = [
        sys.executable,
        "-m",
        "pdd",
        "generate",
        str(prompt_path.relative_to(project_root)),
        "--output",
        str(code_path.relative_to(project_root)),
        "--force",
    ]
    if model:
        cmd.extend(["--model", model])
    completed = subprocess.run(
        cmd,
        cwd=project_root,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"pdd generate failed ({completed.returncode}): {completed.stderr.strip()}"
        )


def _status_from_validation(validation: dict[str, str], key: str) -> Optional[bool]:
    if key not in validation:
        return None
    normalized = (validation.get(key) or "").strip().lower()
    if not normalized:
        return None
    if normalized in _PASS_TOKENS:
        return True
    if "fail" in normalized or "error" in normalized:
        return False
    return None


def _policy_configured(project_root: Path, manifest: Optional[ManifestView]) -> bool:
    policy_paths = (
        project_root / ".pdd" / "policy.yml",
        project_root / ".pdd" / "policy.yaml",
        project_root / "policy.yml",
        project_root / "policy.yaml",
    )
    return manifest is not None or any(path.is_file() for path in policy_paths)


def run_drift(
    devunit: str,
    project_root: Path,
    *,
    runs: int = 1,
    model: Optional[str] = None,
    from_evidence: Optional[Path] = None,
    code_file: Optional[Path] = None,
    dry_run: bool = False,
) -> DriftReport:
    prompt_path, resolved_code, manifest = _load_manifest_paths(
        devunit,
        project_root,
        from_evidence,
    )
    code_path = code_file.resolve() if code_file else resolved_code

    snapshots: list[RunSnapshot] = []
    hashes: list[str] = []
    apis: list[list[str]] = []

    validation = manifest.validation if manifest else {}
    policy_is_configured = _policy_configured(project_root, manifest)

    for _ in range(runs):
        if not dry_run:
            _regenerate_code(
                prompt_path,
                code_path,
                model=model,
                project_root=project_root,
            )

        code_hash = _sha256_file(code_path)
        api = _public_api(code_path)
        tests = _discover_tests(code_path, project_root)
        tests_ok = _run_pytest(tests, project_root)

        stories_ok = _status_from_validation(validation, "detect_stories")
        if stories_ok is None:
            stories_ok = True

        verify_ok = _status_from_validation(validation, "verify")
        if verify_ok is None:
            verify_ok = True

        if policy_is_configured:
            policy_ok = run_gate_policy(project_root, target=devunit).passed
        else:
            policy_ok = True

        snapshots.append(
            RunSnapshot(
                run_index=len(snapshots) + 1,
                code_sha256=code_hash,
                public_api=api,
                tests_passed=tests_ok,
                stories_passed=stories_ok,
                verify_passed=verify_ok,
                policy_passed=policy_ok,
            )
        )
        hashes.append(code_hash)
        apis.append(api)

    public_api_unchanged = all(api == apis[0] for api in apis)
    implementation_changed = len(set(hashes)) > 1
    behavior_unchanged = all(
        snap.tests_passed
        and snap.stories_passed
        and snap.verify_passed
        and snap.policy_passed
        for snap in snapshots
    )
    status = "stable" if public_api_unchanged and behavior_unchanged else "unstable"

    return DriftReport(
        devunit=devunit,
        prompt_path=str(prompt_path),
        code_path=str(code_path),
        runs=runs,
        snapshots=snapshots,
        public_api_unchanged=public_api_unchanged,
        implementation_changed=implementation_changed,
        behavior_unchanged=behavior_unchanged,
        status=status,
        dry_run=dry_run,
    )
