"""Run orchestration (design.md §3.2 stage 4).

For each (scenario, size, trial):

1. verify the manifest against ``manifests.lock`` (freeze enforcement),
2. materialize a fresh variant (sha-verified) and ``git init`` a baseline,
3. start the recording proxy (and, for the ``mock`` arm, the mock provider),
4. run the agent (mock behavior or an external command with the proxy's
   base URL injected into its environment),
5. run visible tests and the hidden verifier (hidden tree never enters the
   variant),
6. attribute snapshots, analyze the iteration trajectory, and write one run
   record (JSONL line) plus raw artifacts under ``reports/<run_id>/``.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

from harness.context_snapshots.attribution import TreeIndex, extract_payload_text
from harness.context_snapshots.proxy import HEALTH_PATH
from harness.context_snapshots.iteration_analyzer import analyze_run
from harness.context_snapshots.proxy import RecordingProxy
from harness.distractors.manifest import load_manifest, manifest_sha256, verify_lockfile
from harness.runner.agent_launcher import (
    AgentLaunchError,
    FileAgentLauncher,
    launch_local_subprocess,
)
from harness.runner.env_freeze import FreezeConfig, FrozenEnvironment
from harness.runner.metrics import build_run_record, read_changed_paths
from harness.runner.mock_agent import MockAgent, MockModelServer
from harness.runner.variant_builder import materialize_variant


def verifier_env(src_path: Path) -> dict:
    """Environment for visible/hidden verification (design §4.1.2 determinism).

    Built from the operator environment but with ``PYTEST_*`` scrubbed, so an
    ambient ``PYTEST_ADDOPTS`` (e.g. ``-k`` / ``-p``) cannot silently change
    which assertions run — a run's pass/fail must depend only on the code and
    the committed scenario, never on the shell it was launched from. Combined
    with the per-``hidden/`` and per-``core/`` ``pytest.ini``, verification is
    isolated from the surrounding repo's pytest config as well.
    """
    import os

    env = {k: v for k, v in os.environ.items() if not k.startswith("PYTEST_")}
    env["PYTHONPATH"] = str(src_path)
    return env


@dataclass
class RunConfig:
    scenario_dir: Path  # holds core/, hidden/, scenario.json, task.md, (pool/)
    distractors_dir: Path  # ManifestWriter output (manifests/ + generated/ + lock)
    reports_dir: Path
    work_root: Path  # fresh variants are materialized under here
    arm: str = "mock"  # "mock" or "command"
    agent_command: list[str] | None = None  # for arm="command"; placeholders expanded
    upstream_base_url: str | None = None  # real provider for arm="command"
    mock_behavior: str = "oracle"  # oracle | wrong_file | noop
    mock_read_distractor_count: int = 2
    timeout_seconds: float = 1800.0
    check_baseline: bool = True  # assert visible-pass/hidden-fail before the agent
    # §8.1.1 run-environment freeze — required for real command-arm runs. When
    # set, the agent executes under a sanitized, fingerprinted environment
    # built fresh per trial; `registered_env_fingerprint` (when given) must
    # match the built environment or the run aborts.
    freeze: FreezeConfig | None = None
    registered_env_fingerprint: str | None = None
    allow_unfrozen_command: bool = False
    # Interface the recording proxy binds to. Default loopback (agent is a
    # local subprocess). In the container hard tier (harness/runner/container),
    # the agent runs in a separate no-egress netns and reaches the proxy over
    # the sandbox network, so the proxy binds to the sandbox-facing address.
    proxy_host: str = "127.0.0.1"
    # When the proxy binds to 0.0.0.0, the agent still needs a routable
    # service address (for example `runner` inside docker compose).
    proxy_advertised_host: str | None = None
    # Command-arm launch path: either a local subprocess or the shared-filesystem
    # worker protocol used by the isolated container tier.
    agent_launcher: str = "local"  # "local" or "container_worker"
    agent_request_dir: Path | None = None

    def __post_init__(self) -> None:
        for name in ("scenario_dir", "distractors_dir", "reports_dir", "work_root"):
            setattr(self, name, Path(getattr(self, name)))
        if self.agent_request_dir is not None:
            self.agent_request_dir = Path(self.agent_request_dir)
        if isinstance(self.freeze, dict):
            self.freeze = FreezeConfig(**self.freeze)
        if self.arm not in {"mock", "command"}:
            raise ValueError('RunConfig.arm must be "mock" or "command"')
        if self.agent_launcher not in {"local", "container_worker"}:
            raise ValueError('RunConfig.agent_launcher must be "local" or "container_worker"')
        if self.arm == "command" and not self.allow_unfrozen_command:
            if self.freeze is None:
                raise ValueError(
                    'arm="command" requires RunConfig.freeze; set '
                    "allow_unfrozen_command=True only for harness development runs"
                )
            if not self.registered_env_fingerprint:
                raise ValueError(
                    'arm="command" requires registered_env_fingerprint; set '
                    "allow_unfrozen_command=True only for harness development runs"
                )
        if self.agent_launcher == "container_worker" and self.agent_request_dir is None:
            raise ValueError(
                'agent_launcher="container_worker" requires agent_request_dir'
            )


@dataclass
class TrialResult:
    record: dict
    report_dir: Path


class ExperimentRunner:
    def __init__(self, config: RunConfig) -> None:
        self.config = config
        self.scenario = json.loads(
            (config.scenario_dir / "scenario.json").read_text(encoding="utf-8")
        )

    # -- helpers -------------------------------------------------------------

    def _expand_command(self, command: list[str], workdir: Path) -> list[str]:
        """Expand harness command placeholders.

        ``{python}`` pins scenario/test helper commands to the interpreter
        running the harness, avoiding ambient ``python3`` mismatches.
        """
        return [
            part.replace("{workdir}", str(workdir)).replace("{python}", sys.executable)
            for part in command
        ]

    def _run(self, command: list[str], cwd: Path, env_extra: dict | None = None,
             timeout: float | None = None) -> subprocess.CompletedProcess:
        env = verifier_env(cwd / "src")
        env.update(env_extra or {})
        return subprocess.run(
            self._expand_command(command, cwd),
            cwd=str(cwd),
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )

    def _visible_pass(self, workdir: Path) -> bool:
        spec = self.scenario["visible_tests"]
        result = self._run(spec["command"], cwd=workdir)
        return result.returncode == spec.get("expected_exit_code", 0)

    def _hidden_pass(self, workdir: Path) -> bool:
        hidden_dir = self.config.scenario_dir / self.scenario["hidden_verifier"]["path"]
        result = subprocess.run(
            self._expand_command(self.scenario["hidden_verifier"]["command"], workdir),
            cwd=str(hidden_dir),
            env=verifier_env(workdir / "src"),
            capture_output=True,
            text=True,
        )
        return result.returncode == 0

    def _git(self, workdir: Path, *args: str) -> None:
        subprocess.run(
            ["git", *args], cwd=str(workdir), check=True, capture_output=True,
            env={"PATH": "/usr/bin:/bin:/usr/local/bin",
                 "GIT_AUTHOR_NAME": "harness", "GIT_AUTHOR_EMAIL": "harness@local",
                 "GIT_COMMITTER_NAME": "harness", "GIT_COMMITTER_EMAIL": "harness@local",
                 "HOME": str(workdir)},
        )

    def _launch_command_agent(
        self,
        *,
        run_id: str,
        command: list[str],
        workdir: Path,
        agent_env: dict[str, str],
    ):
        if self.config.agent_launcher == "local":
            return launch_local_subprocess(
                command=command,
                cwd=workdir,
                env=agent_env,
                timeout_seconds=self.config.timeout_seconds,
            )
        if self.config.agent_launcher == "container_worker":
            launcher = FileAgentLauncher(self.config.agent_request_dir)
            return launcher.launch(
                run_id=run_id,
                command=command,
                cwd=workdir,
                env=agent_env,
                timeout_seconds=self.config.timeout_seconds,
            )
        raise AgentLaunchError(f"unknown launcher: {self.config.agent_launcher}")

    # -- the run -------------------------------------------------------------

    def run_trial(self, size: int, trial_index: int) -> TrialResult:
        config = self.config
        scenario_id = self.scenario["scenario_id"]
        size_label = f"{size}x"
        run_id = f"{scenario_id}.{size_label}.trial{trial_index}"
        report_dir = config.reports_dir / run_id
        if report_dir.exists():
            shutil.rmtree(report_dir)
        report_dir.mkdir(parents=True)

        # 1. Freeze enforcement.
        manifest_path = (
            config.distractors_dir / "manifests" / f"{scenario_id}.{size_label}.json"
        )
        lock_path = config.distractors_dir / "manifests.lock"
        if not verify_lockfile(manifest_path, lock_path):
            raise RuntimeError(
                f"freeze violation: {manifest_path.name} not verified by {lock_path}"
            )
        manifest = load_manifest(manifest_path)

        # 2. Materialize + baseline.
        workdir = config.work_root / run_id
        if workdir.exists():
            shutil.rmtree(workdir)
        materialize_variant(
            core_root=config.scenario_dir / self.scenario["core_path"],
            manifest=manifest,
            destination=workdir,
            pool_root=(
                config.scenario_dir / self.scenario["pool_path"]
                if self.scenario.get("pool_path")
                else None
            ),
            distractors_dir=config.distractors_dir,
        )
        self._git(workdir, "init", "-q")
        self._git(workdir, "add", "-A")
        self._git(workdir, "commit", "-qm", "pre-run baseline")

        if config.check_baseline:
            if not self._visible_pass(workdir):
                raise RuntimeError("baseline violation: visible tests fail pre-run")
            if self._hidden_pass(workdir):
                raise RuntimeError("baseline violation: hidden verifier passes pre-run")

        # 3. Instrumentation.
        mock_server = None
        upstream = config.upstream_base_url
        if config.arm == "mock":
            mock_server = MockModelServer()
            upstream = mock_server.start()
        proxy = RecordingProxy(
            upstream_base_url=upstream,
            archive_dir=report_dir,
            run_id=run_id,
            host=config.proxy_host,
            advertised_host=config.proxy_advertised_host,
        )
        proxy_url = proxy.start()
        (report_dir / "proxy_endpoint.json").write_text(
            json.dumps(
                {
                    "base_url": proxy_url,
                    "health_url": f"{proxy_url}{HEALTH_PATH}",
                    "bind_host": config.proxy_host,
                    "advertised_host": config.proxy_advertised_host or config.proxy_host,
                    "port": proxy.port,
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )

        # 4. Agent.
        timed_out = False
        agent_error = False
        frozen: FrozenEnvironment | None = None
        env_fingerprint: str | None = None
        cli_version: str | None = None
        started = time.monotonic()
        try:
            if config.arm == "mock":
                distractor_reads = [
                    f["upstream_path"] for f in manifest["files"]
                ][: config.mock_read_distractor_count]
                agent = MockAgent(
                    proxy_base_url=proxy_url,
                    workdir=workdir,
                    behavior=config.mock_behavior,
                    files_to_read=distractor_reads + list(self.scenario["target_files"]),
                    oracle_edit=self.scenario.get("oracle_edit"),
                    wrong_file=(manifest["files"][0]["upstream_path"]
                                if manifest["files"] else None),
                )
                task_brief = (
                    config.scenario_dir / self.scenario["task_brief_path"]
                ).read_text(encoding="utf-8")
                agent.run(task_brief=task_brief)
            else:
                command = self._expand_command(config.agent_command or [], workdir)
                if config.freeze is not None:
                    frozen = FrozenEnvironment(
                        config=config.freeze,
                        run_dir=report_dir,
                        proxy_base_url=proxy_url,
                    ).build()
                    if config.registered_env_fingerprint:
                        frozen.verify_fingerprint(config.registered_env_fingerprint)
                    env_fingerprint = frozen.fingerprint()
                    cli_version = frozen.cli_version
                    agent_env = frozen.environment()
                else:
                    # Unfrozen command runs are for harness development only;
                    # every record they produce says so (env_fingerprint null).
                    import os

                    agent_env = dict(os.environ)
                    agent_env["OPENAI_BASE_URL"] = f"{proxy_url}/v1"
                try:
                    completed = self._launch_command_agent(
                        run_id=run_id,
                        command=command,
                        workdir=workdir,
                        agent_env=agent_env,
                    )
                    (report_dir / "agent_process.json").write_text(
                        json.dumps(
                            {
                                "command": completed.command,
                                "returncode": completed.returncode,
                                "stdout": completed.stdout,
                                "stderr": completed.stderr,
                                "timed_out": completed.timed_out,
                                "launcher": completed.launcher,
                            },
                            indent=2,
                        )
                        + "\n",
                        encoding="utf-8",
                    )
                    if completed.timed_out:
                        timed_out = True
                    elif completed.returncode != 0:
                        # A crashed/refused agent is a recorded failed run, not
                        # a cell-killing exception: raising here would abort
                        # every later trial in the cell and lose their data
                        # mid-pilot. The trial is flagged agent_error, its
                        # diagnostics are in agent_process.json, and the cell
                        # continues.
                        agent_error = True
                except AgentLaunchError:
                    raise
        finally:
            if frozen is not None and frozen.home_dir.exists():
                archived = frozen.collect_and_destroy()
                (report_dir / "codex_home_manifest.json").write_text(
                    json.dumps({"archived": archived}, indent=2) + "\n",
                    encoding="utf-8",
                )
            wall_clock = time.monotonic() - started
            proxy.stop()
            if mock_server:
                mock_server.stop()

        # 5. Verification.
        visible_pass = self._visible_pass(workdir)
        hidden_pass = self._hidden_pass(workdir)
        changed_paths = read_changed_paths(workdir)
        (report_dir / "post_run.diff").write_text(
            "\n".join(changed_paths) + "\n", encoding="utf-8"
        )

        # 6. Attribution + trajectory + record.
        distractor_paths = [f["upstream_path"] for f in manifest["files"]]
        tree_index = TreeIndex(workdir, distractor_paths=distractor_paths)
        request_texts = [
            extract_payload_text((report_dir / r.payload_path).read_bytes())
            for r in proxy.records
        ]
        attributions = [tree_index.classify_text(text) for text in request_texts]
        trajectory = analyze_run(proxy.records, attributions)

        core_root = config.scenario_dir / self.scenario["core_path"]
        core_files = [
            p.relative_to(core_root).as_posix()
            for p in core_root.rglob("*")
            if p.is_file()
        ]
        record = build_run_record(
            run_id=run_id,
            scenario_id=scenario_id,
            size=size_label,
            size_multiplier=size,
            trial_index=trial_index,
            arm=config.arm,
            manifest=manifest,
            manifest_sha256=manifest_sha256(manifest_path),
            records=proxy.records,
            attributions=attributions,
            trajectory=trajectory,
            tree_index=tree_index,
            request_texts=request_texts,
            changed_paths=changed_paths,
            target_files=self.scenario["target_files"],
            allowed_edit_globs=self.scenario.get("allowed_edit_globs", []),
            core_files=core_files,
            visible_pass=visible_pass,
            hidden_pass=hidden_pass,
            timed_out=timed_out,
            agent_error=agent_error,
            wall_clock_seconds=wall_clock,
            timeout_seconds=config.timeout_seconds,
            env_fingerprint_sha256=env_fingerprint,
            cli_version=cli_version,
        )
        (report_dir / "run_record.json").write_text(
            json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        with (config.reports_dir / "run_records.jsonl").open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(record, sort_keys=True) + "\n")
        return TrialResult(record=record, report_dir=report_dir)

    def run_cell(self, size: int, trials: int) -> list[TrialResult]:
        return [self.run_trial(size, t) for t in range(trials)]
