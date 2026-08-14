"""Manifest parsing and validation."""

from __future__ import annotations

from pathlib import Path

import pytest

from pdd_k8s.config import ConfigError, config_exists, load_config

VALID = """\
version: 1
cluster:
  name: demo-local
  namespace: demo
services:
  api:
    dev_units: [router, analyzer]
    dockerfile: deploy/Dockerfile
    port: 8000
    health:
      path: /healthz
  web:
    dev_units: [frontend_app]
    dockerfile: frontend/Dockerfile
    port: 3000
"""


def write_manifest(root: Path, body: str) -> Path:
    path = root / ".pdd" / "deployments.yaml"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")
    return path


def test_loads_services_and_cluster(tmp_path: Path) -> None:
    write_manifest(tmp_path, VALID)
    config = load_config(tmp_path)

    assert config.cluster.name == "demo-local"
    assert config.cluster.context == "kind-demo-local"
    assert sorted(config.services) == ["api", "web"]
    assert config.services["api"].dev_units == ["router", "analyzer"]
    assert config.services["api"].health.path == "/healthz"
    assert config.services["api"].image == "pdd-api:local"
    # Defaults apply where the manifest is silent.
    assert config.services["web"].health.path == "/health"
    assert config.services["web"].replicas == 1
    assert config.services["web"].context == "."


def test_cluster_defaults_when_omitted(tmp_path: Path) -> None:
    write_manifest(
        tmp_path,
        "version: 1\nservices:\n  api:\n    dev_units: [r]\n    dockerfile: D\n    port: 80\n",
    )
    config = load_config(tmp_path)
    assert config.cluster.name == "pdd-local"
    assert config.cluster.namespace == "pdd-local"


def test_select_defaults_to_all_sorted(tmp_path: Path) -> None:
    write_manifest(tmp_path, VALID)
    config = load_config(tmp_path)
    assert [service.name for service in config.select([])] == ["api", "web"]
    assert [service.name for service in config.select(["web"])] == ["web"]


def test_select_rejects_unknown_service(tmp_path: Path) -> None:
    write_manifest(tmp_path, VALID)
    config = load_config(tmp_path)
    with pytest.raises(ConfigError, match="unknown service"):
        config.select(["nope"])


def test_dev_unit_owner_maps_back_to_service(tmp_path: Path) -> None:
    write_manifest(tmp_path, VALID)
    config = load_config(tmp_path)
    assert config.dev_unit_owner("analyzer") == "api"
    assert config.dev_unit_owner("frontend_app") == "web"
    assert config.dev_unit_owner("unmapped") is None


def test_missing_manifest_is_reported_not_raised_blindly(tmp_path: Path) -> None:
    assert config_exists(tmp_path) is False
    with pytest.raises(ConfigError, match="pdd-k8s init"):
        load_config(tmp_path)


@pytest.mark.parametrize(
    ("body", "expected"),
    [
        ("version: 2\nservices:\n  a:\n    dev_units: [x]\n    dockerfile: D\n    port: 1\n", "unsupported manifest version"),
        ("version: 1\n", "must define a 'services' mapping"),
        ("", "is empty"),
        ("- a\n- b\n", "YAML mapping"),
        ("version: 1\nservices:\n  API:\n    dev_units: [x]\n    dockerfile: D\n    port: 1\n", "lowercase"),
        ("version: 1\nservices:\n  a:\n    dev_units: []\n    dockerfile: D\n    port: 1\n", "at least 1 item"),
        ("version: 1\nservices:\n  a:\n    dev_units: [x, x]\n    dockerfile: D\n    port: 1\n", "must not repeat"),
        ("version: 1\nservices:\n  a:\n    dev_units: [x]\n    dockerfile: D\n    port: 99999\n", "less than or equal to 65535"),
        ("version: 1\nservices:\n  a:\n    dev_units: [x]\n    dockerfile: D\n    port: 1\n    health:\n      path: health\n", "must start with '/'"),
        ("version: 1\nservices:\n  a:\n    dev_units: [x]\n    dockerfile: D\n    port: 1\n    typo: true\n", "Extra inputs"),
    ],
)
def test_invalid_manifests_are_rejected(tmp_path: Path, body: str, expected: str) -> None:
    write_manifest(tmp_path, body)
    with pytest.raises(ConfigError, match=expected):
        load_config(tmp_path)
