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
import sys
from pathlib import Path
from typing import Any, Sequence

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


class LedgerError(ValueError):
    """Raised when ledger source data cannot safely be rendered."""


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


def _validate_step(step: object, statuses: set[str], index: int) -> None:
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


def validate_ledger(payload: dict[str, Any], plan: Path, source: Path) -> None:
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
    if ledger_generation.get("trust_boundary") != "reviewed-source-only":
        raise LedgerError("ledger_generation.trust_boundary must be reviewed-source-only")
    steps = payload.get("steps")
    if not isinstance(steps, list) or not steps:
        raise LedgerError("ledger source field 'steps' must be a non-empty list")
    for index, step in enumerate(steps):
        _validate_step(step, statuses, index)
    _validate_plan(plan, source, payload)


def render_ledger(plan: Path, output: Path, source: Path | None = None) -> bytes:
    """Validate and return the canonical ledger bytes without writing files."""
    selected_source = source or default_source_path(output)
    payload = load_unique_yaml(selected_source)
    validate_ledger(payload, plan, selected_source)
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
    plan: Path, output: Path, source: Path | None = None, *, check: bool = False
) -> int:
    """Render or verify a ledger, returning a process-compatible exit status."""
    expected = render_ledger(plan, output, source)
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
    return parser.parse_args(arguments)


def main(arguments: Sequence[str] | None = None) -> int:
    """Run the ledger CLI and print actionable validation errors."""
    args = parse_args(arguments)
    try:
        return run(args.plan, args.output, args.source, check=args.check)
    except LedgerError as exc:
        print(f"global-sync ledger error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
