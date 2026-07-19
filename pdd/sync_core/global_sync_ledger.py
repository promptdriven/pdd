"""Render and verify the reviewed global-sync evidence ledger.

The ledger is deliberately rendered from a small, explicit YAML source rather
than extracted from prose.  This module is a renderer and validator: it never
derives a passing evidence state from a plan or from a local command result.
Promotion remains a protected review decision recorded with exact evidence in
the versioned source.
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import sys
from pathlib import Path
from typing import Any, Protocol, Sequence
from urllib.error import URLError
from urllib.parse import urlparse
from urllib.request import Request, urlopen

import yaml


LEDGER_SCHEMA_VERSION = 4
REQUIRED_GATE_STATE_FIELDS = (
    "implemented",
    "local_green",
    "independently_reviewed",
    "hosted_green",
    "merged",
    "released",
    "deployed",
    "certified",
)
SOURCE_MARKER = "<!-- global-sync-ledger-source: {source_name} -->"
GATE_COUNT = 10
SHA1 = re.compile(r"[0-9a-f]{40}")
SHA256 = re.compile(r"[0-9a-f]{64}")
ACTION_RUN_URL = re.compile(r"^/([^/]+/[^/]+)/actions/runs/(\d+)$")
ACTION_JOB_URL = re.compile(r"^/([^/]+/[^/]+)/actions/runs/(\d+)/job/(\d+)$")
CHECK_RUN_URL = re.compile(r"^/([^/]+/[^/]+)/runs/(\d+)$")


class LedgerError(ValueError):
    """Raised when ledger source data cannot safely be rendered."""


class PromotionVerifier(Protocol):  # pylint: disable=too-few-public-methods
    """External boundary that verifies a claimed protected promotion."""

    def verify(self, bundle: dict[str, Any]) -> None:
        """Verify one typed promotion bundle or raise ``LedgerError``."""


class GitHubPromotionVerifier:  # pylint: disable=too-few-public-methods
    """Verify recorded GitHub PR, merge, and successful check claims."""

    def __init__(self) -> None:
        self._responses: dict[str, dict[str, Any]] = {}

    def _get(self, path: str) -> dict[str, Any]:
        if path in self._responses:
            return self._responses[path]
        token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
        headers = {"Accept": "application/vnd.github+json"}
        if token:
            headers["Authorization"] = f"Bearer {token}"
        request = Request(f"https://api.github.com{path}", headers=headers)
        try:
            with urlopen(request, timeout=20) as response:  # nosec B310
                payload = json.loads(response.read().decode("utf-8"))
        except (URLError, OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise LedgerError(f"protected GitHub verification failed for {path}") from exc
        if not isinstance(payload, dict):
            raise LedgerError(f"protected GitHub response is malformed for {path}")
        self._responses[path] = payload
        return payload

    @staticmethod
    def _require_success(payload: dict[str, Any], path: str) -> None:
        if payload.get("conclusion") != "success":
            raise LedgerError(f"protected GitHub check is not successful: {path}")

    def verify(self, bundle: dict[str, Any]) -> None:
        """Compare a claimed promotion bundle with protected GitHub records."""
        verification = _require_mapping(bundle, "protected_verification")
        if verification.get("mode") != "github-pr-checks":
            raise LedgerError("protected verification mode must be github-pr-checks")
        repository = bundle["repository"]
        pull_request = verification.get("pull_request")
        if not isinstance(pull_request, int) or pull_request < 1:
            raise LedgerError("protected GitHub verification requires a positive pull request")
        pull = self._get(f"/repos/{repository}/pulls/{pull_request}")
        head = pull.get("head")
        if not isinstance(head, dict) or head.get("sha") != bundle["head_sha"]:
            raise LedgerError("protected GitHub pull request head SHA does not match")
        if (
            pull.get("merged") is not True
            or pull.get("merge_commit_sha") != bundle["repository_sha"]
        ):
            raise LedgerError("protected GitHub merge SHA does not match")
        for binding in bundle["artifact_bindings"]:
            self._verify_binding(repository, bundle["head_sha"], binding)

    def _verify_binding(
        self, repository: str, head_sha: str, binding: dict[str, Any]
    ) -> None:
        kind = binding["kind"]
        if kind == "signed_digest":
            return
        parsed = _parse_github_binding(binding)
        if parsed["repository"] != repository:
            raise LedgerError("artifact binding repository does not match promotion claim")
        if kind == "github_actions_run":
            run_data = self._get(f"/repos/{repository}/actions/runs/{parsed['run_id']}")
            self._require_success(run_data, "actions run")
            if run_data.get("head_sha") != head_sha:
                raise LedgerError("protected GitHub action run head SHA does not match")
        elif kind == "github_actions_job":
            run_data = self._get(f"/repos/{repository}/actions/runs/{parsed['run_id']}")
            self._require_success(run_data, "actions run")
            if run_data.get("head_sha") != head_sha:
                raise LedgerError("protected GitHub action run head SHA does not match")
            job = self._get(f"/repos/{repository}/actions/jobs/{parsed['job_id']}")
            self._require_success(job, "actions job")
        else:
            check = self._get(f"/repos/{repository}/check-runs/{parsed['check_id']}")
            self._require_success(check, "check run")
            if check.get("head_sha") != head_sha:
                raise LedgerError("protected GitHub check run head SHA does not match")


class _UniqueKeyLoader(yaml.SafeLoader):  # pylint: disable=too-many-ancestors
    """Safe YAML loader that rejects duplicate mapping keys."""


def _construct_mapping(
    loader: _UniqueKeyLoader, node: yaml.MappingNode, deep: bool = False
) -> dict[object, object]:
    """Construct a mapping while reporting the first duplicate key."""
    mapping: dict[object, object] = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=deep)
        try:
            if key in mapping:
                raise LedgerError(f"duplicate YAML key: {key!r}")
        except TypeError as exc:
            raise LedgerError("YAML mapping keys must be scalar") from exc
        mapping[key] = loader.construct_object(value_node, deep=deep)
    return mapping


_UniqueKeyLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _construct_mapping
)


def load_unique_yaml(path: Path) -> dict[str, Any]:
    """Load one regular YAML mapping without accepting duplicate keys."""
    if path.is_symlink() or not path.is_file():
        raise LedgerError(f"YAML input must be a regular file: {path}")
    try:
        payload = yaml.load(path.read_text(encoding="utf-8"), Loader=_UniqueKeyLoader)
    except (OSError, UnicodeDecodeError, yaml.YAMLError) as exc:
        raise LedgerError(f"cannot parse YAML input {path}: {exc}") from exc
    if not isinstance(payload, dict) or not all(
        isinstance(key, str) for key in payload
    ):
        raise LedgerError("ledger source must be a YAML mapping with string keys")
    return payload


def default_source_path(output: Path) -> Path:
    """Return the source path paired with one ledger output path."""
    return output.with_name(f"{output.stem}_source.yaml")


def _require_mapping(payload: dict[str, Any], key: str) -> dict[str, Any]:
    value = payload.get(key)
    if not isinstance(value, dict):
        raise LedgerError(f"ledger source field {key!r} must be a mapping")
    return value


def _require_sha(value: object, field: str) -> str:
    if not isinstance(value, str) or SHA1.fullmatch(value) is None:
        raise LedgerError(f"{field} must be an exact lowercase 40-hex SHA")
    return value


def _parse_github_binding(binding: dict[str, Any]) -> dict[str, str]:
    url = binding.get("url")
    if not isinstance(url, str):
        raise LedgerError("GitHub artifact binding requires a URL")
    parsed = urlparse(url)
    if parsed.scheme != "https" or parsed.netloc != "github.com" or parsed.query:
        raise LedgerError("GitHub artifact binding URL is malformed")
    kind = binding.get("kind")
    matcher = {
        "github_actions_run": ACTION_RUN_URL,
        "github_actions_job": ACTION_JOB_URL,
        "github_check_run": CHECK_RUN_URL,
    }.get(kind)
    match = matcher.fullmatch(parsed.path) if matcher else None
    if match is None:
        raise LedgerError("GitHub artifact binding kind and URL do not match")
    values = match.groups()
    result = {"repository": values[0]}
    if kind in {"github_actions_run", "github_actions_job"}:
        result["run_id"] = values[1]
    if kind == "github_actions_job":
        result["job_id"] = values[2]
    if kind == "github_check_run":
        result["check_id"] = values[1]
    return result


def _validate_promotion_bundle(bundle: object, name: str) -> dict[str, Any]:
    if not isinstance(bundle, dict):
        raise LedgerError(f"promotion bundle {name!r} must be a mapping")
    repository = bundle.get("repository")
    if not isinstance(repository, str) or repository.count("/") != 1:
        raise LedgerError(f"promotion bundle {name!r} repository is malformed")
    _require_sha(bundle.get("repository_sha"), f"promotion bundle {name!r} repository_sha")
    _require_sha(bundle.get("head_sha"), f"promotion bundle {name!r} head_sha")
    command = bundle.get("validation_command")
    if not isinstance(command, str) or not command.strip():
        raise LedgerError(f"promotion bundle {name!r} requires a validation command")
    predicate = _require_mapping(bundle, "machine_predicate")
    if not isinstance(predicate.get("name"), str) or not predicate["name"].strip():
        raise LedgerError(f"promotion bundle {name!r} machine predicate name is missing")
    if predicate.get("result") != "passed":
        raise LedgerError(f"promotion bundle {name!r} machine predicate must be passed")
    bindings = bundle.get("artifact_bindings")
    if not isinstance(bindings, list) or not bindings:
        raise LedgerError(f"promotion bundle {name!r} requires an artifact binding")
    for binding in bindings:
        if not isinstance(binding, dict):
            raise LedgerError(f"promotion bundle {name!r} artifact binding is malformed")
        if binding.get("kind") == "signed_digest":
            digest = binding.get("sha256")
            if not isinstance(digest, str) or SHA256.fullmatch(digest) is None:
                raise LedgerError(f"promotion bundle {name!r} signed digest is malformed")
        else:
            _parse_github_binding(binding)
    return bundle


def _promotion_references(
    record: dict[str, Any], record_name: str
) -> set[str]:
    evidence_state = record["evidence_state"]
    passed_states = [
        name for name in REQUIRED_GATE_STATE_FIELDS if evidence_state[name] == "passed"
    ]
    if record["status"] == "passed":
        if len(passed_states) != len(REQUIRED_GATE_STATE_FIELDS):
            raise LedgerError(f"{record_name}.status cannot pass before every lifecycle state")
        passed_states.append("status")
    elif len(passed_states) == len(REQUIRED_GATE_STATE_FIELDS):
        raise LedgerError(f"{record_name} must be passed when every lifecycle state is passed")
    previous_rank = 2
    ranks = {"pending": 0, "in-progress": 1, "passed": 2}
    for state in REQUIRED_GATE_STATE_FIELDS:
        rank = ranks[evidence_state[state]]
        if rank > previous_rank:
            raise LedgerError(f"{record_name}.evidence_state lifecycle progression is invalid")
        previous_rank = rank
    references = record.get("promotion_evidence", {})
    if not isinstance(references, dict):
        raise LedgerError(f"{record_name}.promotion_evidence must be a mapping")
    if set(references) != set(passed_states):
        raise LedgerError(
            f"{record_name}.promotion_evidence must name exactly every passed state"
        )
    if any(not isinstance(value, str) or not value for value in references.values()):
        raise LedgerError(f"{record_name}.promotion_evidence bundle reference is malformed")
    return set(references.values())


def _require_exact_string_sequence(
    payload: dict[str, Any], key: str, expected: tuple[str, ...]
) -> None:
    value = payload.get(key)
    if not isinstance(value, list) or tuple(value) != expected:
        raise LedgerError(f"ledger source field {key!r} must equal {list(expected)!r}")


def _validate_plan(plan: Path, source: Path, payload: dict[str, Any]) -> None:
    if plan.is_symlink() or not plan.is_file():
        raise LedgerError(f"plan input must be a regular file: {plan}")
    controlling_plan = payload.get("controlling_plan")
    if not isinstance(controlling_plan, str) or not controlling_plan:
        raise LedgerError("ledger source field 'controlling_plan' must be a non-empty string")
    marker = SOURCE_MARKER.format(source_name=source.name)
    try:
        plan_text = plan.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise LedgerError(f"cannot read plan input {plan}: {exc}") from exc
    if marker not in plan_text:
        raise LedgerError(
            f"plan does not authorize source {source.name!r}; expected marker {marker!r}"
        )


def _validate_step(step: object, statuses: set[str], index: int) -> set[str]:
    if not isinstance(step, dict):
        raise LedgerError(f"steps[{index}] must be a mapping")
    if step.get("status") not in statuses:
        raise LedgerError(f"steps[{index}].status is not in status_vocabulary")
    evidence_state = step.get("evidence_state")
    if not isinstance(evidence_state, dict):
        raise LedgerError(f"steps[{index}].evidence_state must be a mapping")
    if set(evidence_state) != set(REQUIRED_GATE_STATE_FIELDS):
        raise LedgerError(
            f"steps[{index}].evidence_state must contain exactly the required gate states"
        )
    if any(value not in statuses for value in evidence_state.values()):
        raise LedgerError(f"steps[{index}].evidence_state contains an invalid state")
    required_predicate = step.get("required_predicate")
    if not isinstance(required_predicate, dict):
        raise LedgerError(f"steps[{index}].required_predicate must be a mapping")
    if step["status"] == "passed" and not required_predicate:
        raise LedgerError(f"steps[{index}].required_predicate cannot be empty when passed")
    return _promotion_references(step, f"steps[{index}]")


def validate_ledger(  # pylint: disable=too-many-locals,too-many-branches
    payload: dict[str, Any],
    plan: Path,
    source: Path,
    *,
    verify_remote: bool = False,
    promotion_verifier: PromotionVerifier | None = None,
) -> None:
    """Reject schema/state drift before preserving the reviewed source bytes."""
    if payload.get("schema_version") != LEDGER_SCHEMA_VERSION:
        raise LedgerError(f"ledger schema_version must be {LEDGER_SCHEMA_VERSION}")
    statuses_value = payload.get("status_vocabulary")
    if not isinstance(statuses_value, list) or not all(
        isinstance(status, str) for status in statuses_value
    ):
        raise LedgerError("ledger status_vocabulary must be a list of strings")
    statuses = set(statuses_value)
    if len(statuses_value) != len(statuses) or statuses != {"pending", "in-progress", "passed"}:
        raise LedgerError("ledger status_vocabulary must contain pending, in-progress, passed")
    if payload.get("evidence_state_vocabulary") != statuses_value:
        raise LedgerError("ledger evidence_state_vocabulary must match status_vocabulary")
    _require_exact_string_sequence(
        payload, "required_gate_state_fields", REQUIRED_GATE_STATE_FIELDS
    )
    ledger_generation = _require_mapping(payload, "ledger_generation")
    if ledger_generation.get("status") not in statuses:
        raise LedgerError("ledger_generation.status is not in status_vocabulary")
    generation_state = ledger_generation.get("evidence_state")
    if not isinstance(generation_state, dict) or set(generation_state) != set(
        REQUIRED_GATE_STATE_FIELDS
    ):
        raise LedgerError(
            "ledger_generation.evidence_state must contain exactly the required gate states"
        )
    if any(value not in statuses for value in generation_state.values()):
        raise LedgerError("ledger_generation.evidence_state contains an invalid state")
    if ledger_generation.get("source") != source.name:
        raise LedgerError("ledger_generation.source must name the exact source file")
    if ledger_generation.get("trust_boundary") != "source-claims-require-protected-verification":
        raise LedgerError(
            "ledger_generation.trust_boundary must require protected verification"
        )
    steps = payload.get("steps")
    if not isinstance(steps, list) or len(steps) != GATE_COUNT:
        raise LedgerError(f"ledger source field 'steps' must contain exactly {GATE_COUNT} gates")
    bundle_references = _promotion_references(ledger_generation, "ledger_generation")
    for index, step in enumerate(steps):
        if not isinstance(step, dict) or step.get("order") != index + 1:
            raise LedgerError(f"steps[{index}].order must be stable order {index + 1}")
        bundle_references.update(_validate_step(step, statuses, index))
    live_rebaseline = _require_mapping(payload, "live_rebaseline")
    if live_rebaseline.get("gates_required") != GATE_COUNT:
        raise LedgerError(f"live_rebaseline.gates_required must equal {GATE_COUNT}")
    passed_gates = sum(step["status"] == "passed" for step in steps)
    if live_rebaseline.get("gates_passed") != passed_gates:
        raise LedgerError("live_rebaseline.gates_passed does not match passed gate statuses")
    bundles = _require_mapping(payload, "promotion_bundles")
    if set(bundles) != bundle_references:
        raise LedgerError("promotion_bundles must contain exactly the referenced promotion claims")
    validated_bundles = {
        name: _validate_promotion_bundle(bundle, name) for name, bundle in bundles.items()
    }
    if verify_remote:
        verifier = promotion_verifier or GitHubPromotionVerifier()
        for name in sorted(bundle_references):
            verifier.verify(validated_bundles[name])
    _validate_plan(plan, source, payload)


def render_ledger(
    plan: Path,
    output: Path,
    source: Path | None = None,
    *,
    verify_remote: bool = False,
    promotion_verifier: PromotionVerifier | None = None,
) -> bytes:
    """Validate and return the canonical ledger bytes without writing files."""
    selected_source = source or default_source_path(output)
    payload = load_unique_yaml(selected_source)
    validate_ledger(
        payload,
        plan,
        selected_source,
        verify_remote=verify_remote,
        promotion_verifier=promotion_verifier,
    )
    try:
        return selected_source.read_bytes()
    except OSError as exc:
        raise LedgerError(f"cannot read ledger source {selected_source}: {exc}") from exc


def _drift_message(expected: bytes, actual: bytes, output: Path) -> str:
    expected_lines = expected.decode("utf-8").splitlines(keepends=True)
    actual_lines = actual.decode("utf-8").splitlines(keepends=True)
    diff = "".join(
        difflib.unified_diff(
            actual_lines,
            expected_lines,
            fromfile=f"committed/{output}",
            tofile=f"regenerated/{output}",
        )
    )
    return f"global-sync ledger drift: {output} differs from its reviewed source\n{diff}"


def run(
    plan: Path,
    output: Path,
    source: Path | None = None,
    *,
    check: bool = False,
    verify_remote: bool = False,
) -> int:
    """Render or verify a ledger, returning a process-compatible exit status."""
    expected = render_ledger(plan, output, source, verify_remote=verify_remote)
    if check:
        if output.is_symlink() or not output.is_file():
            print(
                f"global-sync ledger drift: committed ledger is missing: {output}",
                file=sys.stderr,
            )
            return 1
        actual = output.read_bytes()
        if actual != expected:
            print(_drift_message(expected, actual, output), file=sys.stderr, end="")
            return 1
        print(f"global-sync ledger check passed: {output}")
        return 0
    if output.is_symlink():
        raise LedgerError(f"ledger output must not be a symlink: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(expected)
    print(f"generated global-sync ledger: {output}")
    return 0


def parse_args(arguments: Sequence[str] | None = None) -> argparse.Namespace:
    """Parse the intentionally small standalone ledger CLI."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, required=True, help="ratified controlling plan")
    parser.add_argument("--output", type=Path, required=True, help="generated ledger path")
    parser.add_argument("--source", type=Path, help="reviewed YAML source path")
    parser.add_argument(
        "--check", action="store_true", help="fail without writing when ledger bytes drift"
    )
    parser.add_argument(
        "--verify-remote",
        action="store_true",
        help="verify GitHub promotion claims against protected remote metadata",
    )
    return parser.parse_args(arguments)


def main(arguments: Sequence[str] | None = None) -> int:
    """Run the ledger CLI and print actionable validation errors."""
    args = parse_args(arguments)
    try:
        return run(
            args.plan,
            args.output,
            args.source,
            check=args.check,
            verify_remote=args.verify_remote,
        )
    except LedgerError as exc:
        print(f"global-sync ledger error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
