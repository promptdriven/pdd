"""Canonical synchronization certification and recovery commands."""
# pylint: disable=duplicate-code

from __future__ import annotations

import json
import os
import shlex
import uuid
from datetime import datetime, timezone
from pathlib import Path
from pathlib import PurePosixPath
from typing import Optional

import click

from ..sync_core import (
    CanonicalReportOptions,
    FingerprintProvenance,
    FingerprintRecord,
    FingerprintStore,
    GlobalCertificateOptions,
    NightlyObservation,
    PathPolicy,
    PlannedWrite,
    RepositoryTarget,
    SemanticStatus,
    TransactionManager,
    attestation_signer_from_environment,
    build_canonical_report,
    build_global_certificate,
    build_unit_manifest,
    build_unit_snapshot,
    candidate_artifact_policy_from_environment,
    checker_identity_from_environment,
    encode_fingerprint,
    finalize_unit,
    load_committed_aliases,
    load_verification_profiles,
    require_valid_manifest,
    run_lifecycle_matrix,
    signer_from_environment,
)
from ..sync_core.git_io import resolve_git_commit
from ..sync_core.runner import (
    RunnerConfig,
    _load_vitest_toolchain_descriptor,
    _playwright_toolchain_identity,
    _protected_command_error,
    _playwright_command_error,
    _vitest_command_error,
)
from .. import __version__


def _repository_path(name: str, cwd: Path) -> Path:
    """Resolve a named checkout without silently choosing another repository."""
    normalized = name.replace("-", "_")
    configured = os.environ.get(f"PDD_CERTIFY_{normalized.upper()}_PATH")
    candidates = [Path(configured)] if configured else []
    candidates.extend([cwd, cwd.parent / name, cwd.parent / normalized])
    candidates.extend(parent for parent in cwd.parents if parent.name == name)
    candidates.extend(parent for parent in cwd.parents if parent.name == normalized)
    for candidate in candidates:
        is_named = candidate.name in {name, normalized}
        is_pdd_checkout = name == "pdd" and (candidate / "pdd" / "__init__.py").is_file()
        if (is_named or is_pdd_checkout) and (candidate / ".git").exists():
            return candidate.resolve()
    raise ValueError(f"cannot resolve repository checkout: {name}")


def _global_targets(
    repositories: str, merge_group: str, cwd: Path
) -> tuple[RepositoryTarget, ...]:
    if len(merge_group) != 40 or any(
        character not in "0123456789abcdef" for character in merge_group
    ):
        raise ValueError("--merge-group must be an exact lowercase commit SHA")
    names = tuple(item.strip() for item in repositories.split(",") if item.strip())
    if names != ("pdd", "pdd_cloud"):
        raise ValueError("--repos must name exactly pdd,pdd_cloud")
    targets = []
    for name in names:
        path = _repository_path(name, cwd)
        if name == "pdd":
            head_ref = merge_group
            base_ref = os.environ.get(
                "PDD_CERTIFY_PDD_BASE_SHA", f"{merge_group}^1"
            )
        else:
            head_ref = os.environ.get("PDD_CERTIFY_PDD_CLOUD_HEAD_SHA")
            base_ref = os.environ.get("PDD_CERTIFY_PDD_CLOUD_BASE_SHA")
            if not head_ref or not base_ref:
                raise ValueError(
                    "protected runner must set PDD_CERTIFY_PDD_CLOUD_BASE_SHA "
                    "and PDD_CERTIFY_PDD_CLOUD_HEAD_SHA"
                )
            if (
                len(head_ref) != 40
                or len(base_ref) != 40
                or any(character not in "0123456789abcdef" for character in head_ref + base_ref)
                or head_ref == base_ref
            ):
                raise ValueError(
                    "protected pdd_cloud base/head must be distinct lowercase commit SHAs"
                )
        targets.append(RepositoryTarget(name, path, base_ref, head_ref))
    return tuple(targets)


def _load_nightly_observation(path: Path | None) -> NightlyObservation | None:
    """Load protected workflow observations without accepting schema drift."""
    if path is None:
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    required = {
        "complete_scan",
        "ledgers_deleted_before_scan",
        "normal_scan_writes",
        "injected_canary_detected",
        "injected_canary_outcome",
        "post_canary_rerun_writes",
    }
    if not isinstance(payload, dict) or set(payload) != required:
        raise ValueError("nightly observation schema is invalid")
    if (
        not all(
            isinstance(payload[name], bool)
            for name in (
                "complete_scan",
                "ledgers_deleted_before_scan",
                "injected_canary_detected",
            )
        )
        or not all(
            isinstance(payload[name], int)
            and not isinstance(payload[name], bool)
            and payload[name] >= 0
            for name in ("normal_scan_writes", "post_canary_rerun_writes")
        )
        or payload["injected_canary_outcome"] not in {"REPAIRED", "BLOCKED"}
    ):
        raise ValueError("nightly observation types are invalid")
    observation = NightlyObservation(
        payload["complete_scan"],
        payload["ledgers_deleted_before_scan"],
        payload["normal_scan_writes"],
        payload["injected_canary_detected"],
        payload["injected_canary_outcome"],
        payload["post_canary_rerun_writes"],
    )
    return observation


def _protected_command(value: str | None, option: str, cwd: Path) -> tuple[str, ...] | None:
    """Parse a protected validator argv and reject candidate-local path inputs."""
    if value is None or not value.strip():
        return None
    try:
        command = tuple(shlex.split(value))
    except ValueError as exc:
        raise click.ClickException(f"{option} is malformed") from exc
    if not command:
        return None
    error = _protected_command_error(cwd, command)
    if error is not None:
        raise click.ClickException(f"{option}: {error}")
    return command


def _protected_playwright_command(
    value: str | None, cwd: Path
) -> tuple[str, ...] | None:
    """Parse the fixed executable-plus-entrypoint Playwright descriptor."""
    command = _protected_command(value, "--playwright-command", cwd)
    if command is None:
        return None
    if len(command) != 2 or not Path(command[1]).expanduser().is_absolute():
        raise click.ClickException(
            "--playwright-command must contain exactly an absolute executable "
            "and absolute external CLI entrypoint"
        )
    if any(part.startswith("-") for part in command[1:]):
        raise click.ClickException(
            "--playwright-command must not contain interpreter options"
        )
    return command


def _runner_config_from_options(
    options: dict[str, object], cwd: Path
) -> RunnerConfig:
    # pylint: disable=too-many-locals
    """Build trusted validator configuration from protected CLI/env options."""
    jest_command = options.get("jest_command")
    vitest_command = options.get("vitest_command")
    vitest_manifest = options.get("vitest_toolchain_manifest")
    protected_vitest = _protected_command(
        vitest_command if isinstance(vitest_command, str) else None,
        "--vitest-command",
        cwd,
    )
    if protected_vitest is not None and len(protected_vitest) != 2:
        raise click.ClickException(
            "--vitest-command must contain exactly an absolute launcher and entrypoint"
        )
    manifest_path = (
        Path(vitest_manifest).expanduser().resolve()
        if isinstance(vitest_manifest, str) and vitest_manifest else None
    )
    if (protected_vitest is None) != (manifest_path is None):
        raise click.ClickException(
            "--vitest-command and --vitest-toolchain-manifest are required together"
        )
    if protected_vitest is not None:
        error = _vitest_command_error(cwd, protected_vitest)
        if error is not None:
            raise click.ClickException(f"--vitest-command: {error}")
    playwright_command = options.get("playwright_command")
    playwright_manifest = options.get("playwright_toolchain_manifest")
    protected_playwright = _protected_playwright_command(
        playwright_command if isinstance(playwright_command, str) else None,
        cwd,
    )
    playwright_manifest_path = (
        Path(playwright_manifest).expanduser().resolve()
        if isinstance(playwright_manifest, str) and playwright_manifest else None
    )
    if (protected_playwright is None) != (playwright_manifest_path is None):
        raise click.ClickException(
            "--playwright-command and --playwright-toolchain-manifest are required together"
        )
    if protected_playwright is not None:
        error = _playwright_command_error(cwd, protected_playwright)
        if error is not None:
            raise click.ClickException(f"--playwright-command: {error}")
    config = RunnerConfig(
        jest_command=_protected_command(
            jest_command if isinstance(jest_command, str) else None,
            "--jest-command",
            cwd,
        ),
        vitest_command=protected_vitest,
        vitest_toolchain_manifest=manifest_path,
        playwright_command=protected_playwright,
        playwright_toolchain_manifest=playwright_manifest_path,
    )
    if protected_vitest is not None:
        try:
            descriptor = _load_vitest_toolchain_descriptor(cwd, config)
        except (OSError, ValueError) as exc:
            raise click.ClickException(f"invalid Vitest toolchain: {exc}") from exc
        config = RunnerConfig(
            jest_command=config.jest_command,
            vitest_command=config.vitest_command,
            vitest_toolchain_manifest=config.vitest_toolchain_manifest,
            vitest_toolchain_identity=descriptor.identity,
            playwright_command=config.playwright_command,
            playwright_toolchain_manifest=config.playwright_toolchain_manifest,
            adapter_identities=config.adapter_identities,
        )
    if protected_playwright is not None:
        try:
            identity = _playwright_toolchain_identity(
                cwd, protected_playwright, playwright_manifest_path
            )
        except (OSError, ValueError) as exc:
            raise click.ClickException(f"invalid Playwright toolchain: {exc}") from exc
        config = RunnerConfig(
            jest_command=config.jest_command,
            vitest_command=config.vitest_command,
            vitest_toolchain_manifest=config.vitest_toolchain_manifest,
            vitest_toolchain_identity=config.vitest_toolchain_identity,
            playwright_command=config.playwright_command,
            playwright_toolchain_manifest=config.playwright_toolchain_manifest,
            playwright_toolchain_identity=identity,
            adapter_identities=config.adapter_identities,
        )
    return config


@click.command("certify")
@click.option("--base-ref", default="HEAD", show_default=True)
@click.option("--head-ref", default="HEAD", show_default=True)
@click.option(
    "--replay-ledger",
    type=click.Path(path_type=Path),
    envvar="PDD_ATTESTATION_REPLAY_LEDGER",
)
@click.option("--module", "modules", multiple=True)
@click.option("--repos", help="Comma-separated repositories for global certification.")
@click.option("--merge-group", help="Exact protected PDD merge-group commit SHA.")
@click.option("--full-inventory", is_flag=True)
@click.option("--run-lifecycle-matrix", "run_matrix", is_flag=True)
@click.option("--require-nightly-streak", type=click.IntRange(min=7))
@click.option(
    "--nightly-ledger",
    type=click.Path(path_type=Path, dir_okay=False),
    envvar="PDD_NIGHTLY_CERTIFICATE_LEDGER",
)
@click.option(
    "--nightly-observation",
    type=click.Path(path_type=Path, dir_okay=False),
    envvar="PDD_NIGHTLY_OBSERVATION",
)
@click.option("--output", type=click.Path(path_type=Path, dir_okay=False))
@click.pass_context
def certify(
    ctx: click.Context,
    **options,
) -> None:
    # pylint: disable=too-many-locals
    """Produce the strict machine-verifiable canonical sync report."""
    ctx.ensure_object(dict)
    ctx.obj["_suppress_result_summary"] = True
    base_ref = str(options["base_ref"])
    head_ref = str(options["head_ref"])
    trust_root = Path(
        os.environ.get(
            "PDD_SYNC_TRUST_ROOT", Path.home() / ".pdd/trust/global-sync"
        )
    )
    modules = tuple(str(item) for item in options["modules"])
    output_value = options.get("output")
    output: Optional[Path] = Path(output_value) if output_value is not None else None
    try:
        repositories = options.get("repos")
        replay_value = options.get("replay_ledger")
        replay_ledger = (
            Path(replay_value)
            if replay_value is not None
            else trust_root / ("replay" if repositories is not None else "single.json")
        )
        if repositories is not None:
            required = {
                "--merge-group": options.get("merge_group"),
                "--full-inventory": options.get("full_inventory"),
                "--run-lifecycle-matrix": options.get("run_matrix"),
                "--require-nightly-streak": options.get("require_nightly_streak"),
            }
            missing = [name for name, value in required.items() if not value]
            if missing:
                raise ValueError("global certification requires " + ", ".join(missing))
            targets = _global_targets(
                str(repositories), str(options["merge_group"]), Path.cwd().resolve()
            )
            if replay_ledger.exists() and not replay_ledger.is_dir():
                raise ValueError("global --replay-ledger must be a directory")
            replay_ledger.mkdir(mode=0o700, parents=True, exist_ok=True)
            candidate_policy = candidate_artifact_policy_from_environment()
            candidate_policy.replay_ledger_path = (
                replay_ledger / "candidate-artifacts.json"
            )
            report = build_global_certificate(
                targets,
                GlobalCertificateOptions(
                    replay_ledger_root=replay_ledger,
                    lifecycle_result=run_lifecycle_matrix(
                        targets[0].path,
                        candidate_wheel=(
                            Path(os.environ["PDD_CANDIDATE_WHEEL"])
                            if "PDD_CANDIDATE_WHEEL" in os.environ
                            else None
                        ),
                        candidate_wheelhouse=(
                            Path(os.environ["PDD_CANDIDATE_WHEELHOUSE"])
                            if "PDD_CANDIDATE_WHEELHOUSE" in os.environ
                            else None
                        ),
                        candidate_runtime_lock=(
                            Path(os.environ["PDD_CANDIDATE_RUNTIME_LOCK"])
                            if "PDD_CANDIDATE_RUNTIME_LOCK" in os.environ
                            else None
                        ),
                        candidate_attestation=(
                            Path(os.environ["PDD_CANDIDATE_BUILD_ATTESTATION"])
                            if "PDD_CANDIDATE_BUILD_ATTESTATION" in os.environ
                            else None
                        ),
                        candidate_artifact_policy=candidate_policy,
                        cloud_root=targets[1].path,
                        cloud_base_ref=targets[1].base_ref,
                        cloud_head_ref=targets[1].head_ref,
                    ),
                    nightly_ledger=(
                        Path(options["nightly_ledger"])
                        if options.get("nightly_ledger") is not None
                        else trust_root / "nightly.jsonl"
                    ),
                    required_nightly_streak=int(options["require_nightly_streak"]),
                    checker_identity=checker_identity_from_environment(),
                    candidate_artifact_policy=candidate_policy,
                    nightly_observation=_load_nightly_observation(
                        options.get("nightly_observation")
                    ),
                ),
                signer=signer_from_environment(),
            )
        else:
            report = build_canonical_report(
                Path.cwd(),
                CanonicalReportOptions(
                    base_ref=base_ref,
                    head_ref=head_ref,
                    modules=modules,
                    replay_ledger_path=replay_ledger,
                ),
            )
    except (OSError, RuntimeError, ValueError) as exc:
        report = {"schema_version": 1, "ok": False, "errors": [str(exc)]}
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if output is not None:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(encoded, encoding="utf-8")
    click.echo(encoded, nl=False)
    if not report.get("ok"):
        raise click.exceptions.Exit(1)


@click.command("recover")
@click.option("--transaction", "transaction_id", required=True)
@click.pass_context
def recover(ctx: click.Context, transaction_id: str) -> None:
    """Explicitly recover one crash-durable synchronization transaction."""
    ctx.ensure_object(dict)
    root = Path.cwd()
    head = resolve_git_commit(root, "HEAD")
    result = TransactionManager(root).recover(
        transaction_id,
        alias_policy_loader=lambda: PathPolicy(
            root,
            approved_aliases=load_committed_aliases(root, head),
            base_ref=head,
            head_ref=head,
        ),
    )
    click.echo(
        json.dumps(
            {
                "transaction_id": result.transaction_id,
                "phase": result.phase.value,
                "changed_paths": [path.as_posix() for path in result.changed_paths],
                "no_op": result.no_op,
            },
            indent=2,
            sort_keys=True,
        )
    )


@click.command("baseline")
@click.option("--module", required=True, help="Exact repository-relative prompt path.")
@click.option("--reviewed-by", required=True)
@click.option("--reason", required=True)
@click.pass_context
def baseline(ctx: click.Context, module: str, reviewed_by: str, reason: str) -> None:
    # pylint: disable=too-many-locals
    """Record reviewed current bytes as CURRENT plus semantic UNKNOWN."""
    ctx.ensure_object(dict)
    root = Path.cwd().resolve()
    head = resolve_git_commit(root, "HEAD")
    manifest = build_unit_manifest(root, base_ref=head, head_ref=head)
    try:
        require_valid_manifest(manifest)
    except ValueError as exc:
        raise click.ClickException(str(exc)) from exc
    wanted = PurePosixPath(module)
    matches = [
        unit for unit in manifest.managed_units if unit.unit_id.prompt_relpath == wanted
    ]
    if len(matches) != 1:
        raise click.ClickException(
            f"baseline requires exactly one managed prompt match: {module}"
        )
    profiles = load_verification_profiles(root, manifest)
    profile = profiles.for_unit(matches[0].unit_id)
    if profile is None:
        raise click.ClickException("baseline requires a protected verification profile")
    snapshot = build_unit_snapshot(root, manifest, matches[0], profile)
    transaction_id = f"baseline-{uuid.uuid4()}"
    provenance = FingerprintProvenance(
        "baseline-reset",
        f"pdd baseline --module {module}",
        transaction_id,
        head,
        datetime.now(timezone.utc).isoformat(),
        __version__,
        reviewed_by.strip(),
        reason.strip(),
    )
    record = FingerprintRecord(
        snapshot, 2, 2, provenance, SemanticStatus.UNKNOWN, None
    )
    store = FingerprintStore(root)
    store.validate(record)
    relpath = store.path_for(record.snapshot.unit_id).relative_to(root)
    manager = TransactionManager(root)
    manager.prepare(
        transaction_id,
        (
            PlannedWrite(
                PurePosixPath(relpath.as_posix()),
                encode_fingerprint(record),
                "100644",
            ),
        ),
    )
    result = manager.commit(transaction_id)
    click.echo(
        json.dumps(
            {
                "transaction_id": result.transaction_id,
                "baseline": "CURRENT",
                "semantic": "UNKNOWN",
                "fingerprint": relpath.as_posix(),
            },
            indent=2,
            sort_keys=True,
        )
    )


@click.command("validate")
@click.option("--module", required=True, help="Exact repository-relative prompt path.")
@click.option("--base-ref", required=True, help="Protected base commit or ref.")
@click.option("--head-ref", default="HEAD", show_default=True)
@click.option(
    "--jest-command",
    envvar="PDD_SYNC_JEST_COMMAND",
    help="Protected absolute external Jest command argv.",
)
@click.option(
    "--vitest-command",
    envvar="PDD_SYNC_VITEST_COMMAND",
    help="Protected absolute external Vitest command argv.",
)
@click.option(
    "--vitest-toolchain-manifest",
    envvar="PDD_SYNC_VITEST_TOOLCHAIN_MANIFEST",
    type=click.Path(path_type=Path),
    help="Protected external Node/Vitest toolchain closure manifest.",
)
@click.option(
    "--playwright-command",
    envvar="PDD_SYNC_PLAYWRIGHT_COMMAND",
    help="Protected absolute external Playwright command argv.",
)
@click.option(
    "--playwright-toolchain-manifest",
    envvar="PDD_SYNC_PLAYWRIGHT_TOOLCHAIN_MANIFEST",
    type=click.Path(path_type=Path),
    help="Protected external Playwright toolchain manifest.",
)
@click.pass_context
def validate(
    ctx: click.Context,
    module: str,
    base_ref: str,
    head_ref: str,
    jest_command: str | None,
    vitest_command: str | None,
    vitest_toolchain_manifest: Path | None,
    playwright_command: str | None,
    playwright_toolchain_manifest: Path | None,
) -> None:
    # pylint: disable=too-many-arguments,too-many-positional-arguments
    """Run protected obligations and transactionally finalize trusted evidence."""
    ctx.ensure_object(dict)
    root = Path.cwd().resolve()
    result = finalize_unit(
        root,
        PurePosixPath(module),
        base_ref=base_ref,
        head_ref=head_ref,
        signer=attestation_signer_from_environment(),
        config=_runner_config_from_options(
            {
                "jest_command": jest_command,
                "vitest_command": vitest_command,
                "vitest_toolchain_manifest": str(vitest_toolchain_manifest)
                if vitest_toolchain_manifest else None,
                "playwright_command": playwright_command,
                "playwright_toolchain_manifest": str(playwright_toolchain_manifest)
                if playwright_toolchain_manifest else None,
            },
            root,
        ),
    )
    click.echo(
        json.dumps(
            {
                "transaction_id": result.transaction.transaction_id,
                "attestation_id": result.attestation_id,
                "fingerprint": result.fingerprint_path.as_posix(),
                "semantic": "VERIFIED",
            },
            indent=2,
            sort_keys=True,
        )
    )
