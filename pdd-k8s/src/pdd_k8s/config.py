"""Deployment manifest parsing for ``.pdd/deployments.yaml``.

A deployment manifest maps PDD Dev Units onto independently runnable services.
Dev Units are implementation units, not pods: a service names the subset of Dev
Units whose generated code ships together inside one container image.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

import yaml
from pydantic import BaseModel, ConfigDict, Field, field_validator

CONFIG_RELATIVE_PATH = Path(".pdd") / "deployments.yaml"

_SERVICE_NAME_HINT = (
    "Service names become Kubernetes object names, so use lowercase letters, "
    "digits and dashes only."
)


class ConfigError(Exception):
    """Raised when a deployment manifest is missing, unreadable or invalid."""


class HealthCheck(BaseModel):
    """HTTP readiness probe for a service container."""

    model_config = ConfigDict(extra="forbid")

    path: str = Field(default="/health")
    initial_delay_seconds: int = Field(default=2, ge=0)
    period_seconds: int = Field(default=5, ge=1)
    failure_threshold: int = Field(default=6, ge=1)

    @field_validator("path")
    @classmethod
    def _absolute_path(cls, value: str) -> str:
        if not value.startswith("/"):
            raise ValueError("health.path must start with '/'")
        return value


class ServiceSpec(BaseModel):
    """One deployable service assembled from one or more Dev Units."""

    model_config = ConfigDict(extra="forbid")

    name: str = Field(exclude=True)
    dev_units: list[str] = Field(min_length=1)
    dockerfile: str
    context: str = Field(default=".")
    port: int = Field(ge=1, le=65535)
    replicas: int = Field(default=1, ge=0)
    health: HealthCheck = Field(default_factory=HealthCheck)
    env: dict[str, str] = Field(default_factory=dict)

    @field_validator("name")
    @classmethod
    def _kubernetes_safe(cls, value: str) -> str:
        if not value or not all(char.isalnum() or char == "-" for char in value):
            raise ValueError(_SERVICE_NAME_HINT)
        if not value[0].isalpha() or value != value.lower():
            raise ValueError(_SERVICE_NAME_HINT)
        return value

    @field_validator("dev_units")
    @classmethod
    def _unique_dev_units(cls, value: list[str]) -> list[str]:
        if len(set(value)) != len(value):
            raise ValueError("dev_units must not repeat the same Dev Unit")
        return value

    @property
    def image(self) -> str:
        """Local-only image tag; never pushed to a registry."""
        return f"pdd-{self.name}:local"

    def dockerfile_path(self, project_root: Path) -> Path:
        return (project_root / self.dockerfile).resolve()

    def context_path(self, project_root: Path) -> Path:
        return (project_root / self.context).resolve()


class ClusterSpec(BaseModel):
    """The named local cluster PDD is allowed to manage."""

    model_config = ConfigDict(extra="forbid")

    name: str = Field(default="pdd-local")
    namespace: str = Field(default="pdd-local")

    @property
    def context(self) -> str:
        """kubectl context created by ``kind create cluster``."""
        return f"kind-{self.name}"


class DeploymentConfig(BaseModel):
    """A parsed ``.pdd/deployments.yaml`` bound to its project root."""

    model_config = ConfigDict(extra="forbid")

    version: int = Field(default=1)
    cluster: ClusterSpec = Field(default_factory=ClusterSpec)
    services: dict[str, ServiceSpec]
    project_root: Path = Field(exclude=True)

    @field_validator("version")
    @classmethod
    def _supported_version(cls, value: int) -> int:
        if value != 1:
            raise ValueError(f"unsupported manifest version {value}; expected 1")
        return value

    @field_validator("services")
    @classmethod
    def _at_least_one_service(cls, value: dict[str, ServiceSpec]) -> dict[str, ServiceSpec]:
        if not value:
            raise ValueError("at least one service must be defined")
        return value

    def select(self, names: list[str] | tuple[str, ...]) -> list[ServiceSpec]:
        """Resolve service names, defaulting to every service when none given."""
        if not names:
            return [self.services[key] for key in sorted(self.services)]
        unknown = [name for name in names if name not in self.services]
        if unknown:
            known = ", ".join(sorted(self.services)) or "none"
            raise ConfigError(f"unknown service(s): {', '.join(unknown)}. Defined services: {known}")
        return [self.services[name] for name in names]

    def dev_unit_owner(self, dev_unit: str) -> str | None:
        """Return the service a Dev Unit is deployed by, if any."""
        for name, service in sorted(self.services.items()):
            if dev_unit in service.dev_units:
                return name
        return None


def config_path(project_root: Path) -> Path:
    """Absolute path of the deployment manifest for a project."""
    return project_root / CONFIG_RELATIVE_PATH


def config_exists(project_root: Path) -> bool:
    """True when the project has opted in to local service orchestration."""
    return config_path(project_root).is_file()


def load_config(project_root: Path) -> DeploymentConfig:
    """Load and validate the project's deployment manifest.

    Raises:
        ConfigError: the manifest is missing, malformed or fails validation.
    """
    root = Path(project_root).resolve()
    path = config_path(root)
    if not path.is_file():
        raise ConfigError(
            f"No deployment manifest at {path}. Run 'pdd-k8s init' to create one."
        )
    try:
        raw = yaml.safe_load(path.read_text(encoding="utf-8"))
    except (OSError, yaml.YAMLError) as error:
        raise ConfigError(f"Could not read {path}: {error}") from error

    if raw is None:
        raise ConfigError(f"{path} is empty.")
    if not isinstance(raw, dict):
        raise ConfigError(f"{path} must contain a YAML mapping at the top level.")

    services_block = raw.get("services")
    if not isinstance(services_block, dict):
        raise ConfigError(f"{path} must define a 'services' mapping.")

    payload: dict[str, Any] = {
        key: value for key, value in raw.items() if key != "services"
    }
    payload["services"] = {
        name: {**(body if isinstance(body, dict) else {}), "name": name}
        for name, body in services_block.items()
    }
    payload["project_root"] = root

    try:
        return DeploymentConfig.model_validate(payload)
    except Exception as error:  # pydantic ValidationError and value errors
        raise ConfigError(f"Invalid deployment manifest {path}:\n{error}") from error
