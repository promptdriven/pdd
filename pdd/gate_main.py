"""Evidence policy gate for PDD dev units (``pdd checkup gate``)."""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

from .contract_check import check_prompt
from .coverage_contracts import STATUS_UNCHECKED, STATUS_WAIVED, build_coverage
from .evidence_store import (
    ManifestView,
    devunits_dir,
    list_latest_manifests,
    output_freshness,
    prompt_changed_since_manifest,
    prompt_freshness,
    resolve_prompt_path,
)
from .gate_policy import GatePolicy, default_policy, load_policy


@dataclass
class GateFailure:
    code: str
    message: str
    fix_command: str = ""

    def as_dict(self) -> dict[str, str]:
        return {
            "code": self.code,
            "message": self.message,
            "fix_command": self.fix_command,
        }


@dataclass
class GateResult:
    passed: bool
    failures: list[GateFailure] = field(default_factory=list)
    policy: GatePolicy = field(default_factory=default_policy)
    manifests_checked: int = 0

    @property
    def exit_code(self) -> int:
        return 0 if self.passed else 1

    def as_dict(self) -> dict[str, Any]:
        return {
            "passed": self.passed,
            "exit_code": self.exit_code,
            "manifests_checked": self.manifests_checked,
            "policy": self.policy.as_dict(),
            "failures": [failure.as_dict() for failure in self.failures],
        }


_PASS_STATUSES = frozenset({"pass", "passed", "ok", "success"})


def _validation_passes(status: str) -> bool:
    """True only for explicit pass outcomes from evidence manifests."""
    return (status or "").strip().lower() in _PASS_STATUSES


def _append_skipped_validation_failure(
    failures: list[GateFailure],
    *,
    manifest: ManifestView,
    manifest_key: str,
    policy: GatePolicy,
) -> bool:
    """Record skip/not_applicable failures when policy disallows them."""
    if manifest_key == "verify" and not policy.allows("skipped_verify"):
        failures.append(
            GateFailure(
                code="skipped_verify",
                message=f"{manifest.basename}: verify was skipped against policy",
                fix_command="Re-run without --skip-verify",
            )
        )
        return True
    if manifest_key == "unit_tests" and not policy.allows("skipped_tests"):
        failures.append(
            GateFailure(
                code="skipped_tests",
                message=f"{manifest.basename}: unit tests were skipped against policy",
                fix_command="Re-run without --skip-tests",
            )
        )
        return True
    return False


def _check_validation_flags(
    manifest: ManifestView,
    policy: GatePolicy,
) -> list[GateFailure]:
    failures: list[GateFailure] = []
    validation = manifest.validation
    checks = (
        ("stories_pass", "detect_stories", "pdd detect --stories"),
        ("verify_pass", "verify", "pdd verify <prompt>"),
        ("unit_tests_pass", "unit_tests", "pytest <tests>"),
    )
    for policy_key, manifest_key, fix in checks:
        if not policy.requires(policy_key):
            continue
        status = validation.get(manifest_key, "missing")
        normalized = (status or "").strip().lower()
        if normalized == "missing":
            failures.append(
                GateFailure(
                    code=f"{policy_key}_missing",
                    message=(
                        f"No validation.{manifest_key} recorded in "
                        f"{manifest.path.name}"
                    ),
                    fix_command=f"Run a PDD command with --evidence for {manifest.basename}",
                )
            )
            continue
        if _validation_passes(status):
            continue
        if normalized == "not_available":
            failures.append(
                GateFailure(
                    code=f"{manifest_key}_not_available",
                    message=(
                        f"{manifest.basename}: validation.{manifest_key} is "
                        f"not_available (required check was not recorded)"
                    ),
                    fix_command=f"Run a PDD command with --evidence for {manifest.basename}",
                )
            )
            continue
        if normalized == "not_applicable":
            if _append_skipped_validation_failure(
                failures, manifest=manifest, manifest_key=manifest_key, policy=policy
            ):
                continue
            failures.append(
                GateFailure(
                    code=policy_key,
                    message=(
                        f"{manifest.basename}: validation.{manifest_key} is "
                        f"not_applicable but policy requires {policy_key}"
                    ),
                    fix_command=fix,
                )
            )
            continue
        if normalized in {"skip", "skipped"}:
            if _append_skipped_validation_failure(
                failures, manifest=manifest, manifest_key=manifest_key, policy=policy
            ):
                continue
            failures.append(
                GateFailure(
                    code=policy_key,
                    message=(
                        f"{manifest.basename}: validation.{manifest_key}={status!r}"
                    ),
                    fix_command=fix,
                )
            )
            continue
        failures.append(
            GateFailure(
                code=policy_key,
                message=(
                    f"{manifest.basename}: validation.{manifest_key}={status!r}"
                ),
                fix_command=fix,
            )
        )
    if policy.requires("stories_pass") and prompt_changed_since_manifest(manifest):
        failures.append(
            GateFailure(
                code="stories_stale_after_prompt_change",
                message=(
                    f"{manifest.basename}: prompt changed after evidence was recorded; "
                    "story validation must be refreshed"
                ),
                fix_command=f"pdd detect --stories {manifest.basename} --evidence",
            )
        )
    return failures


def _check_output_freshness(
    manifest: ManifestView,
    project_root: Path,
    policy: GatePolicy,
) -> list[GateFailure]:
    if not policy.requires("generated_outputs_fresh"):
        return []
    failures: list[GateFailure] = []
    if manifest.rule_manifest:
        if not prompt_freshness(manifest, project_root):
            failures.append(
                GateFailure(
                    code="stale_prompt",
                    message=(
                        f"Prompt hash differs from evidence manifest for "
                        f"{manifest.prompt_path}"
                    ),
                    fix_command=(
                        f"pdd --evidence sync {manifest.basename}"
                    ),
                )
            )
        return failures

    for item in output_freshness(manifest, project_root):
        if item.fresh:
            continue
        failures.append(
            GateFailure(
                code="stale_output",
                message=(
                    f"{item.path} changed after last evidence manifest "
                    f"(expected {item.expected_sha256[:12]}…)"
                ),
                fix_command=(
                    f"pdd --force sync {manifest.basename} --evidence"
                ),
            )
        )
    return failures


def _check_critical_rules(
    manifest: ManifestView,
    project_root: Path,
    policy: GatePolicy,
    *,
    stories_dir: Optional[Path],
    tests_dir: Optional[Path],
) -> list[GateFailure]:
    if not policy.requires("no_unchecked_critical_rules"):
        return []
    if manifest.prompt_path is None:
        return []

    coverage = build_coverage(manifest.prompt_path, stories_dir, tests_dir)
    if not coverage.rules:
        return []

    failures: list[GateFailure] = []
    for rule in coverage.rules:
        if rule.status in (STATUS_WAIVED,):
            if not policy.allows("waivers"):
                failures.append(
                    GateFailure(
                        code="waiver_not_allowed",
                        message=(
                            f"{rule.rule_id} is waived but policy disallows waivers"
                        ),
                        fix_command="Remove waiver or update .pdd/policy.yml",
                    )
                )
            continue
        if rule.status == STATUS_UNCHECKED:
            failures.append(
                GateFailure(
                    code="unchecked_critical_rule",
                    message=(
                        f"{rule.rule_id} is unchecked in "
                        f"{manifest.prompt_path.relative_to(project_root)}"
                    ),
                    fix_command=(
                        "Add a story, generate a test, or create a waiver."
                    ),
                )
            )
        elif rule.status == "story-only" and not policy.allows("story_only_rules"):
            failures.append(
                GateFailure(
                    code="story_only_rule",
                    message=f"{rule.rule_id} is story-only but policy requires tests",
                    fix_command="pdd test <prompt> or pdd coverage --contracts",
                )
            )
    return failures


def _check_cost_limits(manifest: ManifestView, policy: GatePolicy) -> list[GateFailure]:
    failures: list[GateFailure] = []
    max_cost = policy.limits.max_cost_usd
    if max_cost is None:
        return failures
    cost = float(manifest.generation.get("cost_usd") or 0.0)
    if cost > max_cost:
        failures.append(
            GateFailure(
                code="cost_limit",
                message=(
                    f"{manifest.basename}: run cost ${cost:.2f} exceeds "
                    f"policy limit ${max_cost:.2f}"
                ),
                fix_command="Lower model cost or raise limits.max_cost_usd in policy",
            )
        )
    max_ctx = policy.limits.max_nondeterministic_context_items
    ctx_items = int(manifest.generation.get("nondeterministic_context_items") or 0)
    if ctx_items > max_ctx:
        failures.append(
            GateFailure(
                code="nondeterministic_context_limit",
                message=(
                    f"{manifest.basename}: nondeterministic context items {ctx_items} exceed "
                    f"policy limit {max_ctx}"
                ),
                fix_command=(
                    "Reduce nondeterministic context inputs or raise "
                    "limits.max_nondeterministic_context_items"
                ),
            )
        )
    return failures


def _check_contracts_pipeline(
    manifest: ManifestView,
    policy: GatePolicy,
    *,
    stories_dir: Optional[Path],
    tests_dir: Optional[Path],
) -> list[GateFailure]:
    del stories_dir, tests_dir  # coverage is enforced separately via _check_critical_rules
    if manifest.prompt_path is None:
        return []
    strict = policy.requires("no_unchecked_critical_rules")
    result = check_prompt(manifest.prompt_path, strict=strict)
    errors = result.error_count
    warnings = result.warn_count
    if errors == 0 and not (strict and warnings):
        return []
    detail = result.issues[0].message if result.issues else "contract check failed"
    return [
        GateFailure(
            code="contracts_gate",
            message=f"{manifest.basename}: {detail}",
            fix_command="pdd checkup contract check --strict <prompt>",
        )
    ]


def evaluate_manifest(
    manifest: ManifestView,
    project_root: Path,
    policy: GatePolicy,
    *,
    stories_dir: Optional[Path],
    tests_dir: Optional[Path],
) -> list[GateFailure]:
    failures: list[GateFailure] = []
    failures.extend(_check_validation_flags(manifest, policy))
    failures.extend(_check_output_freshness(manifest, project_root, policy))
    failures.extend(_check_cost_limits(manifest, policy))
    failures.extend(
        _check_critical_rules(
            manifest,
            project_root,
            policy,
            stories_dir=stories_dir,
            tests_dir=tests_dir,
        )
    )
    failures.extend(
        _check_contracts_pipeline(
            manifest,
            policy,
            stories_dir=stories_dir,
            tests_dir=tests_dir,
        )
    )
    return failures


def run_gate_policy(
    project_root: Path,
    *,
    policy_path: Optional[Path] = None,
    target: Optional[str] = None,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
) -> GateResult:
    policy = load_policy(policy_path) if policy_path else default_policy()
    failures: list[GateFailure] = []
    manifests: list[ManifestView] = []

    if target:
        candidate = Path(target)
        if candidate.is_file() and candidate.name.endswith(".latest.json"):
            manifests = [ManifestView.from_file(candidate.resolve(), project_root)]
        else:
            basename = candidate.stem
            latest = devunits_dir(project_root) / f"{basename}.latest.json"
            prompt = resolve_prompt_path(project_root, basename)
            if latest.is_file():
                manifests = [ManifestView.from_file(latest, project_root)]
            elif prompt is not None:
                manifests = [
                    ManifestView(
                        path=latest,
                        basename=basename,
                        schema="missing",
                        raw={},
                        prompt_path=prompt,
                    )
                ]
                failures.append(
                    GateFailure(
                        code="missing_evidence",
                        message=f"No evidence manifest for dev unit {basename}",
                        fix_command=f"pdd --evidence generate {basename}",
                    )
                )
            else:
                failures.append(
                    GateFailure(
                        code="unknown_target",
                        message=f"Could not resolve dev unit or manifest for {target!r}",
                        fix_command="pdd checkup gate --policy .pdd/policy.yml",
                    )
                )
    else:
        for path in list_latest_manifests(project_root):
            manifests.append(ManifestView.from_file(path, project_root))

    checked = 0
    for manifest in manifests:
        checked += 1
        failures.extend(
            evaluate_manifest(
                manifest,
                project_root,
                policy,
                stories_dir=stories_dir,
                tests_dir=tests_dir,
            )
        )

    if not manifests and not failures:
        failures.append(
            GateFailure(
                code="no_manifests",
                message="No evidence manifests found under .pdd/evidence/devunits/",
                fix_command="Run a PDD command with --evidence first",
            )
        )

    return GateResult(
        passed=not failures,
        failures=failures,
        policy=policy,
        manifests_checked=checked,
    )
