"""Preflight environment checks.

``doctor`` exists so a developer learns up front that Docker is not running or
a Dockerfile is missing, rather than reading a Kubernetes error later.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from pathlib import Path

from . import runtime
from .config import DeploymentConfig, config_exists, config_path

OK = "ok"
WARN = "warn"
FAIL = "fail"


@dataclass(frozen=True)
class Check:
    """One environment or configuration assertion."""

    name: str
    status: str
    detail: str
    remedy: str | None = None

    def as_dict(self) -> dict[str, str | None]:
        return asdict(self)


def _tool_check(tool: str, install_hint: str) -> Check:
    path = runtime.tool_path(tool)
    if path is None:
        return Check(tool, FAIL, f"{tool} is not on PATH.", install_hint)
    return Check(tool, OK, path)


def _docker_check() -> Check:
    available, detail = runtime.docker_available()
    if available:
        return Check("docker daemon", OK, detail)
    remedy = (
        "Start Docker Desktop (open -a Docker) and wait for it to report ready."
        if runtime.tool_path("docker")
        else "Install Docker Desktop: https://docs.docker.com/desktop/"
    )
    return Check("docker daemon", FAIL, detail, remedy)


def _cluster_check(config: DeploymentConfig) -> Check:
    name = config.cluster.name
    if runtime.tool_path("kind") is None:
        return Check(f"cluster '{name}'", WARN, "Cannot check: kind is not installed.")
    if name not in runtime.kind_clusters():
        return Check(
            f"cluster '{name}'",
            WARN,
            "Not created yet.",
            f"'pdd-k8s up' will create it, or run: kind create cluster --name {name}",
        )
    if not runtime.kubectl_context_exists(config.cluster.context):
        return Check(
            f"cluster '{name}'",
            FAIL,
            f"kind cluster exists but kubectl context '{config.cluster.context}' is missing.",
            f"Recreate it: kind delete cluster --name {name} && kind create cluster --name {name}",
        )
    reachable = runtime.kubectl(["version", "--output", "json"], context=config.cluster.context, timeout=20)
    if not reachable.ok:
        return Check(f"cluster '{name}'", FAIL, "Cluster is not responding.", reachable.error_text())
    return Check(f"cluster '{name}'", OK, f"Reachable via context {config.cluster.context}.")


def _service_checks(config: DeploymentConfig) -> list[Check]:
    checks: list[Check] = []
    known_dev_units = discover_dev_units(config.project_root)
    for name, service in sorted(config.services.items()):
        dockerfile = service.dockerfile_path(config.project_root)
        if not dockerfile.is_file():
            checks.append(
                Check(
                    f"service '{name}' dockerfile",
                    FAIL,
                    f"{service.dockerfile} does not exist.",
                    "PDD never writes Dockerfiles; add one and point the manifest at it.",
                )
            )
        else:
            checks.append(Check(f"service '{name}' dockerfile", OK, service.dockerfile))

        if not service.context_path(config.project_root).is_dir():
            checks.append(
                Check(f"service '{name}' build context", FAIL, f"{service.context} is not a directory.")
            )

        # Dev Unit discovery is advisory: prompts may live outside the project.
        if known_dev_units:
            missing = [unit for unit in service.dev_units if unit not in known_dev_units]
            if missing:
                checks.append(
                    Check(
                        f"service '{name}' dev units",
                        WARN,
                        f"No prompt found for: {', '.join(missing)}.",
                        "Check the names match your <basename>_<language>.prompt files.",
                    )
                )
            else:
                checks.append(
                    Check(f"service '{name}' dev units", OK, ", ".join(service.dev_units))
                )
    return checks


def discover_dev_units(project_root: Path) -> set[str]:
    """Dev Unit basenames inferred from ``<basename>_<language>.prompt`` files."""
    units: set[str] = set()
    for directory in ("prompts", Path("pdd") / "prompts"):
        prompts_dir = project_root / directory
        if not prompts_dir.is_dir():
            continue
        for prompt in prompts_dir.rglob("*.prompt"):
            basename = prompt.stem.rsplit("_", 1)[0]
            if basename:
                units.add(basename)
    return units


def run_doctor(project_root: Path, config: DeploymentConfig | None = None) -> list[Check]:
    """Run every preflight check, tolerating a missing or invalid manifest."""
    checks = [
        _tool_check("docker", "Install Docker Desktop: https://docs.docker.com/desktop/"),
        _docker_check(),
        _tool_check("kind", "Install kind: brew install kind"),
        _tool_check("kubectl", "Install kubectl: brew install kubectl"),
    ]

    if config is None:
        path = config_path(project_root)
        checks.append(
            Check(
                "deployment manifest",
                FAIL,
                f"{path} is missing or invalid."
                if config_exists(project_root)
                else f"{path} does not exist.",
                "Run 'pdd-k8s init' to create a starter manifest.",
            )
        )
        return checks

    checks.append(
        Check("deployment manifest", OK, f"{len(config.services)} service(s) defined.")
    )
    checks.append(_cluster_check(config))
    checks.extend(_service_checks(config))
    return checks


def blocking(checks: list[Check]) -> list[Check]:
    """Checks that must be resolved before a deployment can proceed."""
    return [check for check in checks if check.status == FAIL]
