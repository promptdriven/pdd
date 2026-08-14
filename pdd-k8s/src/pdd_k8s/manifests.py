"""Plain Kubernetes manifest generation.

Deliberately no Helm: generated manifests are printable, diffable and can be
applied by hand, which keeps the first release easy to inspect and trust.
"""

from __future__ import annotations

from typing import Any

import yaml

from .config import ClusterSpec, ServiceSpec

MANAGED_BY = "pdd"
MANAGED_SELECTOR = f"app.kubernetes.io/managed-by={MANAGED_BY}"


def service_labels(service: ServiceSpec) -> dict[str, str]:
    """Labels identifying a PDD-managed workload."""
    return {
        "app.kubernetes.io/name": service.name,
        "app.kubernetes.io/managed-by": MANAGED_BY,
        "app.kubernetes.io/part-of": "pdd-local-services",
    }


def service_selector(service: ServiceSpec) -> str:
    """Label selector matching exactly one service's objects."""
    return f"{MANAGED_SELECTOR},app.kubernetes.io/name={service.name}"


def namespace_manifest(cluster: ClusterSpec) -> dict[str, Any]:
    return {
        "apiVersion": "v1",
        "kind": "Namespace",
        "metadata": {
            "name": cluster.namespace,
            "labels": {"app.kubernetes.io/managed-by": MANAGED_BY},
        },
    }


def deployment_manifest(service: ServiceSpec, cluster: ClusterSpec) -> dict[str, Any]:
    """Deployment for one service, annotated with the Dev Units it carries."""
    labels = service_labels(service)
    return {
        "apiVersion": "apps/v1",
        "kind": "Deployment",
        "metadata": {
            "name": service.name,
            "namespace": cluster.namespace,
            "labels": labels,
            "annotations": {"pdd.dev/dev-units": ",".join(service.dev_units)},
        },
        "spec": {
            "replicas": service.replicas,
            "selector": {"matchLabels": labels},
            "template": {
                "metadata": {"labels": labels},
                "spec": {
                    "containers": [
                        {
                            "name": service.name,
                            "image": service.image,
                            # Images are side-loaded into kind, never pulled.
                            "imagePullPolicy": "IfNotPresent",
                            "ports": [{"containerPort": service.port, "name": "http"}],
                            "env": [
                                {"name": key, "value": value}
                                for key, value in sorted(service.env.items())
                            ],
                            "readinessProbe": {
                                "httpGet": {"path": service.health.path, "port": service.port},
                                "initialDelaySeconds": service.health.initial_delay_seconds,
                                "periodSeconds": service.health.period_seconds,
                                "failureThreshold": service.health.failure_threshold,
                            },
                        }
                    ]
                },
            },
        },
    }


def service_manifest(service: ServiceSpec, cluster: ClusterSpec) -> dict[str, Any]:
    return {
        "apiVersion": "v1",
        "kind": "Service",
        "metadata": {
            "name": service.name,
            "namespace": cluster.namespace,
            "labels": service_labels(service),
        },
        "spec": {
            "selector": service_labels(service),
            "ports": [{"port": service.port, "targetPort": service.port, "name": "http"}],
        },
    }


class _NoAliasDumper(yaml.SafeDumper):
    """Repeat shared label blocks instead of emitting YAML anchors.

    Anchors are valid and kubectl accepts them, but they make a generated
    manifest harder to read and to copy a single object out of.
    """

    def ignore_aliases(self, data: Any) -> bool:  # noqa: D102 - PyYAML hook
        return True


def render(services: list[ServiceSpec], cluster: ClusterSpec) -> str:
    """Render a multi-document YAML bundle for the given services."""
    documents: list[dict[str, Any]] = [namespace_manifest(cluster)]
    for service in services:
        documents.append(deployment_manifest(service, cluster))
        documents.append(service_manifest(service, cluster))
    return yaml.dump_all(
        documents, Dumper=_NoAliasDumper, sort_keys=False, default_flow_style=False
    )
