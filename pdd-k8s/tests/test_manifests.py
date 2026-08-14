"""Generated Kubernetes manifests."""

from __future__ import annotations

import yaml

from pdd_k8s.config import ClusterSpec, ServiceSpec
from pdd_k8s.manifests import MANAGED_SELECTOR, render, service_selector

CLUSTER = ClusterSpec(name="demo-local", namespace="demo")
SERVICE = ServiceSpec(
    name="api",
    dev_units=["router", "analyzer"],
    dockerfile="deploy/Dockerfile",
    port=8000,
    env={"LOG_LEVEL": "info"},
)


def documents() -> list[dict]:
    return list(yaml.safe_load_all(render([SERVICE], CLUSTER)))


def test_bundle_contains_namespace_deployment_and_service() -> None:
    assert [doc["kind"] for doc in documents()] == ["Namespace", "Deployment", "Service"]


def test_deployment_records_dev_units_and_probe() -> None:
    deployment = documents()[1]
    container = deployment["spec"]["template"]["spec"]["containers"][0]

    assert deployment["metadata"]["annotations"]["pdd.dev/dev-units"] == "router,analyzer"
    assert deployment["metadata"]["namespace"] == "demo"
    assert container["image"] == "pdd-api:local"
    # Images are side-loaded into kind; pulling would fail for a local-only tag.
    assert container["imagePullPolicy"] == "IfNotPresent"
    assert container["readinessProbe"]["httpGet"] == {"path": "/health", "port": 8000}
    assert container["env"] == [{"name": "LOG_LEVEL", "value": "info"}]


def test_everything_is_labelled_managed_by_pdd() -> None:
    for doc in documents():
        assert doc["metadata"]["labels"]["app.kubernetes.io/managed-by"] == "pdd"


def test_selectors_scope_to_pdd_and_to_one_service() -> None:
    assert MANAGED_SELECTOR == "app.kubernetes.io/managed-by=pdd"
    assert service_selector(SERVICE) == "app.kubernetes.io/managed-by=pdd,app.kubernetes.io/name=api"


def test_zero_replicas_is_preserved() -> None:
    scaled = SERVICE.model_copy(update={"replicas": 0})
    deployment = list(yaml.safe_load_all(render([scaled], CLUSTER)))[1]
    assert deployment["spec"]["replicas"] == 0
