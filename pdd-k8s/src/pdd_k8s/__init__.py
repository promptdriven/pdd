"""pdd-k8s — opt-in local service orchestration for PDD projects.

PDD Dev Units are implementation units, not pods. This companion package lets a
project explicitly declare which Dev Units combine into an independently
runnable service, then run those services on a named local Kubernetes cluster.
Projects without ``.pdd/deployments.yaml`` are entirely unaffected.
"""

from __future__ import annotations

from .api import (
    deploy,
    describe,
    doctor_report,
    is_configured,
    service_logs,
    stop,
)
from .config import CONFIG_RELATIVE_PATH, ConfigError, DeploymentConfig, load_config

__version__ = "0.1.0"

__all__ = [
    "CONFIG_RELATIVE_PATH",
    "ConfigError",
    "DeploymentConfig",
    "__version__",
    "deploy",
    "describe",
    "doctor_report",
    "is_configured",
    "load_config",
    "service_logs",
    "stop",
]
