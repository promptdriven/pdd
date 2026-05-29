"""Regeneration stability checks for PDD dev units (``pdd checkup drift``)."""
from __future__ import annotations

import ast
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

from .evidence_store import ManifestView, resolve_prompt_path

try:
    from .evidence_manifest import resolve_test_output_paths
except ImportError:  # pragma: no cover
    resolve_test_output_paths = None  # type: ignore[assignment,misc]

try:
    from .gate_main import run_gate_policy as _run_gate_policy_impl

    _GATE_POLICY_AVAILABLE = True
except ModuleNotFoundError:  # pragma: no cover - optional until gate lands on main
    _GATE_POLICY_AVAILABLE = False

    def _run_gate_policy_impl(*_args, **_kwargs):
        class _Result:
            passed = False

        return _Result()

DEFAULT_MAX_COST_USD = 20.0
_COST_RE = re.compile(r"(?:Total\s+)?Cost:\s*\$([0-9]+(?:\.[0-9]+)?)", re.IGNORECASE)
_POLICY_VALIDATION_KEYS = ("policy", "gate", "checkup_gate", "policy_gate")
_SKIP_VALIDATION_STATUSES = frozenset(
    {"", "not_applicable", "not_available", "skipped"}
)


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
    baseline_public_api: list[str] = field(default_factory=list)
    public_api_unchanged: bool = True
    implementation_changed: bool = False
    behavior_unchanged: bool = True
    status: str = "stable"
    dry_run: bool = False
    max_cost_usd: Optional[float] = None
    total_cost_usd: float = 0.0
    cost_budget_exceeded: bool = False
    policy_check_skipped: bool = False
    policy_check_unavailable: bool = False

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
        completed_runs = len(self.snapshots)
        return {
            "devunit": self.devunit,
            "prompt_path": self.prompt_path,
            "code_path": self.code_path,
            "runs": self.runs,
            "dry_run": self.dry_run,
            "status": self.status,
            "baseline_public_api": self.baseline_public_api,
            "public_api_unchanged": self.public_api_unchanged,
            "implementation_changed": self.implementation_changed,
            "behavior_unchanged": self.behavior_unchanged,
            "total_cost_usd": self.total_cost_usd,
            "cost_budget_exceeded": self.cost_budget_exceeded,
            "policy_check_skipped": self.policy_check_skipped,
            "policy_check_unavailable": self.policy_check_unavailable,
            "max_cost_usd": self.max_cost_usd,
            "tests": f"passed {tests_passed}/{completed_runs or self.runs}",
            "stories": f"passed {stories_passed}/{completed_runs or self.runs}",
            "verify": f"passed {verify_passed}/{completed_runs or self.runs}",
            "policy": f"passed {policy_passed}/{completed_runs or self.runs}",
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


def _parse_cost_usd(stdout: str, stderr: str) -> float:
    combined = f"{stdout}\n{stderr}"
    total = 0.0
    for match in _COST_RE.finditer(combined):
        total += float(match.group(1))
    return total


def _regenerate_code(
    prompt_path: Path,
    output_path: Path,
    *,
    model: Optional[str],
    project_root: Path,
) -> float:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        output_rel = output_path.relative_to(project_root)
    except ValueError:
        output_rel = output_path

    cmd = [
        sys.executable,
        "-m",
        "pdd",
        "generate",
        str(prompt_path.relative_to(project_root)),
        "--output",
        str(output_rel),
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
    return _parse_cost_usd(completed.stdout, completed.stderr)


def _discover_tests(code_path: Path, project_root: Path) -> list[Path]:
    module = code_path.stem
    candidates = [
        project_root / "tests" / f"test_{module}.py",
        project_root / "tests" / f"test_{module.replace('_python', '')}.py",
    ]
    return [path for path in candidates if path.is_file()]


def _candidate_relative_path(code_path: Path, project_root: Path) -> Path:
    try:
        return code_path.relative_to(project_root)
    except ValueError:
        return Path(code_path.name)


def _ignore_cache_dir(_directory: str, names: list[str]) -> set[str]:
    return {name for name in names if name == "__pycache__"}


def _copy_project_subtree(source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(source, destination, ignore=_ignore_cache_dir)


def _copy_test_support_files(
    project_root: Path,
    overlay_root: Path,
    test_paths: list[Path],
) -> Path:
    """Mirror discovered tests, local helpers, and ``conftest.py`` files into the overlay."""
    overlay_tests = overlay_root / "tests"
    for test_path in test_paths:
        rel_test = test_path.relative_to(project_root)
        dest_test = overlay_root / rel_test
        dest_test.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(test_path, dest_test)
        for helper in test_path.parent.glob("*.py"):
            if helper.name == test_path.name or helper.name.startswith("test_"):
                continue
            rel_helper = helper.relative_to(project_root)
            dest_helper = overlay_root / rel_helper
            dest_helper.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(helper, dest_helper)

    project_tests = project_root / "tests"
    if project_tests.is_dir():
        for conftest in project_tests.rglob("conftest.py"):
            rel_conftest = conftest.relative_to(project_root)
            dest_conftest = overlay_root / rel_conftest
            dest_conftest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(conftest, dest_conftest)

    return overlay_tests


def _build_pytest_overlay(
    candidate: Path,
    code_path: Path,
    project_root: Path,
    overlay_root: Path,
) -> Optional[Path]:
    """Build an overlay with project package deps and the candidate replacing baseline."""
    rel = _candidate_relative_path(code_path, project_root)
    package_rel = rel.parent
    if package_rel != Path("."):
        source_package = project_root / package_rel
        if source_package.is_dir():
            _copy_project_subtree(source_package, overlay_root / package_rel)

    module_dest = overlay_root / rel
    module_dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(candidate, module_dest)

    tests = _discover_tests(code_path, project_root)
    if not tests:
        return None

    return _copy_test_support_files(project_root, overlay_root, tests)


def _run_pytest_for_candidate(
    candidate: Path,
    code_path: Path,
    project_root: Path,
    sandbox_root: Path,
) -> bool:
    tests = _discover_tests(code_path, project_root)
    if not tests:
        return True

    overlay_root = sandbox_root / "pytest-overlay"
    if overlay_root.exists():
        shutil.rmtree(overlay_root)
    overlay_root.mkdir(parents=True, exist_ok=True)

    overlay_tests = _build_pytest_overlay(
        candidate,
        code_path,
        project_root,
        overlay_root,
    )
    if overlay_tests is None:
        return True

    env = os.environ.copy()
    env["PYTHONPATH"] = str(overlay_root)
    cmd = [sys.executable, "-m", "pytest", "-q", str(overlay_tests)]
    completed = subprocess.run(
        cmd,
        cwd=overlay_root,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )
    return completed.returncode == 0


def _validation_key_configured(manifest: Optional[ManifestView], keys: tuple[str, ...]) -> bool:
    if manifest is None:
        return False
    for key in keys:
        status = (manifest.validation.get(key) or "").strip().lower()
        if status and status not in _SKIP_VALIDATION_STATUSES:
            return True
    return False


def _stories_configured(manifest: Optional[ManifestView]) -> bool:
    return _validation_key_configured(manifest, ("detect_stories",))


def _verify_configured(manifest: Optional[ManifestView]) -> bool:
    return _validation_key_configured(manifest, ("verify",))


def _policy_configured(project_root: Path, manifest: Optional[ManifestView]) -> bool:
    policy_paths = (
        project_root / ".pdd" / "policy.yml",
        project_root / ".pdd" / "policy.yaml",
        project_root / "policy.yml",
        project_root / "policy.yaml",
    )
    if any(path.is_file() for path in policy_paths):
        return True
    return _validation_key_configured(manifest, _POLICY_VALIDATION_KEYS)


def _run_stories_check(prompt_path: Path, project_root: Path) -> tuple[bool, float]:
    from .user_story_tests import run_user_story_tests  # pylint: disable=import-outside-toplevel

    passed, _, cost, _ = run_user_story_tests(
        prompt_files=[prompt_path],
        prompts_dir=str(project_root / "prompts"),
        quiet=True,
        fail_fast=True,
    )
    return passed, cost


def _run_policy_check(
    project_root: Path,
    manifest: Optional[ManifestView],
    devunit: str,
) -> tuple[bool, bool, bool]:
    """Return ``(passed, skipped, unavailable)`` for policy evaluation."""
    if not _policy_configured(project_root, manifest):
        return True, True, False
    if not _GATE_POLICY_AVAILABLE:
        return False, False, True
    return _run_gate_policy_impl(project_root, target=devunit).passed, False, False


def _run_verify_check(
    prompt_path: Path,
    candidate: Path,
    code_path: Path,
    project_root: Path,
    work_dir: Path,
    *,
    verify_budget_usd: float,
) -> tuple[bool, float]:
    if resolve_test_output_paths is None:
        return True, 0.0

    prompt_copy = work_dir / "prompt" / prompt_path.name
    code_copy = work_dir / "code" / code_path.name
    prompt_copy.parent.mkdir(parents=True, exist_ok=True)
    code_copy.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(prompt_path, prompt_copy)
    shutil.copy2(candidate, code_copy)

    program_paths = resolve_test_output_paths(
        prompt_copy,
        code_copy,
        force=True,
        quiet=True,
    )
    if not program_paths:
        return True, 0.0

    program_source = Path(program_paths[0])
    if not program_source.is_file():
        return True, 0.0

    program_copy = work_dir / "program" / program_source.name
    program_copy.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(program_source, program_copy)

    cmd = [
        sys.executable,
        "-m",
        "pdd",
        "verify",
        str(prompt_copy),
        str(code_copy),
        str(program_copy),
        "--max-attempts",
        "1",
        "--budget",
        str(max(verify_budget_usd, 0.01)),
        "--no-agentic-fallback",
    ]
    completed = subprocess.run(
        cmd,
        cwd=project_root,
        capture_output=True,
        text=True,
        check=False,
    )
    cost = _parse_cost_usd(completed.stdout, completed.stderr)
    return completed.returncode == 0, cost


def _evaluate_candidate(
    candidate: Path,
    *,
    prompt_path: Path,
    code_path: Path,
    project_root: Path,
    manifest: Optional[ManifestView],
    devunit: str,
    sandbox_root: Path,
    work_dir: Path,
    verify_budget_usd: float,
) -> tuple[RunSnapshot, float]:
    extra_cost = 0.0
    tests_ok = _run_pytest_for_candidate(
        candidate, code_path, project_root, sandbox_root
    )

    if _stories_configured(manifest):
        stories_ok, stories_cost = _run_stories_check(prompt_path, project_root)
        extra_cost += stories_cost
    else:
        stories_ok = True

    if _verify_configured(manifest):
        verify_ok, verify_cost = _run_verify_check(
            prompt_path,
            candidate,
            code_path,
            project_root,
            work_dir,
            verify_budget_usd=verify_budget_usd,
        )
        extra_cost += verify_cost
    else:
        verify_ok = True

    policy_ok, _policy_skipped, _policy_unavailable = _run_policy_check(
        project_root,
        manifest,
        devunit,
    )

    return (
        RunSnapshot(
            run_index=0,
            code_sha256=_sha256_file(candidate),
            public_api=_public_api(candidate),
            tests_passed=tests_ok,
            stories_passed=stories_ok,
            verify_passed=verify_ok,
            policy_passed=policy_ok,
        ),
        extra_cost,
    )


def run_drift(
    devunit: str,
    project_root: Path,
    *,
    runs: int = 1,
    model: Optional[str] = None,
    from_evidence: Optional[Path] = None,
    code_file: Optional[Path] = None,
    dry_run: bool = False,
    max_cost_usd: Optional[float] = None,
) -> DriftReport:
    prompt_path, resolved_code, manifest = _load_manifest_paths(
        devunit,
        project_root,
        from_evidence,
    )
    code_path = code_file.resolve() if code_file else resolved_code

    if not code_path.is_file():
        raise FileNotFoundError(f"Code file not found: {code_path}")

    effective_max_cost = max_cost_usd
    if effective_max_cost is None and not dry_run:
        effective_max_cost = DEFAULT_MAX_COST_USD

    baseline_bytes = code_path.read_bytes()
    baseline_api = _public_api(code_path)
    baseline_hash = hashlib.sha256(baseline_bytes).hexdigest()

    snapshots: list[RunSnapshot] = []
    candidate_hashes: list[str] = []
    candidate_apis: list[str] = []
    total_cost = 0.0
    cost_budget_exceeded = False
    policy_check_skipped = not _policy_configured(project_root, manifest)
    policy_check_unavailable = (
        _policy_configured(project_root, manifest) and not _GATE_POLICY_AVAILABLE
    )

    with tempfile.TemporaryDirectory(prefix="pdd-drift-") as temp_name:
        temp_root = Path(temp_name)
        sandbox_root = temp_root / "sandbox"
        sandbox_root.mkdir(parents=True, exist_ok=True)

        for run_index in range(runs):
            work_dir = temp_root / f"run-{run_index + 1}"
            work_dir.mkdir(parents=True, exist_ok=True)

            if dry_run:
                candidate = code_path
            else:
                rel = _candidate_relative_path(code_path, project_root)
                candidate = temp_root / "candidates" / f"run-{run_index + 1}" / rel
                run_cost = _regenerate_code(
                    prompt_path,
                    candidate,
                    model=model,
                    project_root=project_root,
                )
                total_cost += run_cost
                if effective_max_cost is not None and total_cost > effective_max_cost:
                    cost_budget_exceeded = True
                    break

            remaining_budget = (
                max(effective_max_cost - total_cost, 0.01)
                if effective_max_cost is not None
                else 5.0
            )
            snapshot, eval_cost = _evaluate_candidate(
                candidate,
                prompt_path=prompt_path,
                code_path=code_path,
                project_root=project_root,
                manifest=manifest,
                devunit=devunit,
                sandbox_root=sandbox_root,
                work_dir=work_dir,
                verify_budget_usd=remaining_budget,
            )
            total_cost += eval_cost
            if effective_max_cost is not None and total_cost > effective_max_cost:
                cost_budget_exceeded = True
                break

            snapshot.run_index = run_index + 1
            snapshots.append(snapshot)
            candidate_hashes.append(snapshot.code_sha256)
            candidate_apis.append(snapshot.public_api)

    if code_path.read_bytes() != baseline_bytes:
        raise RuntimeError(
            f"Drift check mutated baseline code file: {code_path}. "
            "This should never happen; report a bug."
        )

    public_api_unchanged = bool(candidate_apis) and all(
        api == baseline_api for api in candidate_apis
    )
    implementation_changed = any(h != baseline_hash for h in candidate_hashes) or len(
        set(candidate_hashes)
    ) > 1
    behavior_unchanged = all(
        snap.tests_passed
        and snap.stories_passed
        and snap.verify_passed
        and snap.policy_passed
        for snap in snapshots
    )
    status = (
        "stable"
        if public_api_unchanged and behavior_unchanged and not cost_budget_exceeded
        else "unstable"
    )

    return DriftReport(
        devunit=devunit,
        prompt_path=str(prompt_path),
        code_path=str(code_path),
        runs=runs,
        snapshots=snapshots,
        baseline_public_api=baseline_api,
        public_api_unchanged=public_api_unchanged,
        implementation_changed=implementation_changed,
        behavior_unchanged=behavior_unchanged,
        status=status,
        dry_run=dry_run,
        max_cost_usd=effective_max_cost,
        total_cost_usd=total_cost,
        cost_budget_exceeded=cost_budget_exceeded,
        policy_check_skipped=policy_check_skipped,
        policy_check_unavailable=policy_check_unavailable,
    )
