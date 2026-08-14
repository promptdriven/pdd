"""Deployment lifecycle and status reporting, with external tools faked."""

from __future__ import annotations

from pdd_k8s import orchestrator
from pdd_k8s.config import DeploymentConfig

from .conftest import FakeRuntime, pod, pod_list_json


def api(config: DeploymentConfig) -> list:
    return config.select(["api"])


def test_up_builds_loads_applies_and_waits(config: DeploymentConfig, fake_runtime: FakeRuntime) -> None:
    outcomes = orchestrator.up(config, api(config))

    assert [outcome.ok for outcome in outcomes] == [True]
    assert [step.step for step in outcomes[0].steps] == ["cluster", "build", "load", "apply", "ready"]
    assert fake_runtime.ran("docker build", "--tag", "pdd-api:local")
    assert fake_runtime.ran("kind load docker-image", "pdd-api:local", "--name demo-local")
    assert fake_runtime.ran("kubectl", "apply")
    assert fake_runtime.ran("rollout status deployment/api")


def test_every_kubectl_call_is_pinned_to_the_named_context(
    config: DeploymentConfig, fake_runtime: FakeRuntime
) -> None:
    orchestrator.up(config, api(config))
    kubectl_calls = [call for call in fake_runtime.calls if call[0] == "kubectl"]

    assert kubectl_calls, "expected kubectl to be used"
    for call in kubectl_calls:
        assert call[1:3] == ["--context", "kind-demo-local"]


def test_up_stops_at_the_first_failing_step(config: DeploymentConfig, fake_runtime: FakeRuntime) -> None:
    fake_runtime.when("docker build", returncode=1, stderr="missing base image")
    outcomes = orchestrator.up(config, api(config))

    assert outcomes[0].ok is False
    assert outcomes[0].failure() == "build: missing base image"
    # Nothing is applied to the cluster once the build fails.
    assert not fake_runtime.ran("kubectl", "apply")


def test_missing_dockerfile_fails_before_docker_runs(
    config: DeploymentConfig, fake_runtime: FakeRuntime
) -> None:
    (config.project_root / "deploy" / "Dockerfile").unlink()
    outcomes = orchestrator.up(config, api(config))

    assert outcomes[0].ok is False
    assert "Dockerfile not found" in (outcomes[0].failure() or "")
    assert not fake_runtime.ran("docker build")


def test_failed_rollout_attaches_recent_events(config: DeploymentConfig, fake_runtime: FakeRuntime) -> None:
    fake_runtime.when("rollout status", returncode=1, stderr="timed out")
    fake_runtime.when(
        "get events",
        stdout='{"items":[{"type":"Warning","reason":"BackOff","message":"Back-off restarting",'
               '"involvedObject":{"name":"api-abc"}}]}',
    )
    outcomes = orchestrator.up(config, api(config))

    failure = outcomes[0].failure() or ""
    assert "timed out" in failure
    assert "BackOff" in failure


def test_status_reports_running_service_with_dev_units(
    config: DeploymentConfig, fake_runtime: FakeRuntime
) -> None:
    fake_runtime.when("get pods", stdout=pod_list_json(pod("api-1"), pod("api-2")))
    payload = orchestrator.status(config, config.select([]))

    assert payload["available"] is True
    assert payload["cluster"] == "demo-local"
    service = payload["services"][0]
    assert service["state"] == "running"
    assert service["ready_replicas"] == 2
    assert service["dev_units"] == ["router", "analyzer"]
    assert service["pods"][0]["health"] == "passing"
    assert service["events"] == []


def test_status_surfaces_pending_pods_with_events(
    config: DeploymentConfig, fake_runtime: FakeRuntime
) -> None:
    fake_runtime.when(
        "get pods",
        stdout=pod_list_json(pod("api-1", ready=False, waiting="ImagePullBackOff", phase="Pending")),
    )
    fake_runtime.when(
        "get events",
        stdout='{"items":[{"type":"Warning","reason":"Failed","message":"pull failed",'
               '"involvedObject":{"name":"api-1"}}]}',
    )
    service = orchestrator.status(config, config.select([]))["services"][0]

    assert service["state"] == "pending"
    assert service["ready_replicas"] == 0
    assert service["pods"][0]["health"] == "ImagePullBackOff"
    assert "pull failed" in service["events"][0]


def test_status_reads_node_name_from_pod_spec(
    config: DeploymentConfig, fake_runtime: FakeRuntime
) -> None:
    fake_runtime.when("get pods", stdout=pod_list_json(pod("api-1")))
    pods = orchestrator.status(config, config.select([]))["services"][0]["pods"]
    assert pods[0]["node"] == "demo-local-control-plane"


def test_unscheduled_pod_is_labelled_rather_than_blank(
    config: DeploymentConfig, fake_runtime: FakeRuntime
) -> None:
    pending = pod("api-1", ready=False, phase="Pending")
    pending["spec"] = {}
    fake_runtime.when("get pods", stdout=pod_list_json(pending))
    fake_runtime.when("get events", stdout='{"items":[]}')
    pods = orchestrator.status(config, config.select([]))["services"][0]["pods"]
    assert pods[0]["node"] == "unscheduled"


def test_status_counts_restarts_across_pods(config: DeploymentConfig, fake_runtime: FakeRuntime) -> None:
    fake_runtime.when("get pods", stdout=pod_list_json(pod("api-1", restarts=2), pod("api-2", restarts=3)))
    assert orchestrator.status(config, config.select([]))["services"][0]["restarts"] == 5


def test_status_when_cluster_is_absent_still_lists_services(
    config: DeploymentConfig, fake_runtime: FakeRuntime, monkeypatch
) -> None:
    monkeypatch.setattr(orchestrator.runtime, "kind_clusters", lambda: [])
    payload = orchestrator.status(config, config.select([]))

    assert payload["available"] is False
    assert "not running" in payload["message"]
    # The Dev Unit mapping is static, so it is reported even with no cluster.
    assert payload["services"][0]["dev_units"] == ["router", "analyzer"]
    assert payload["services"][0]["state"] == "not deployed"


def test_status_reports_unreadable_pod_output(config: DeploymentConfig, fake_runtime: FakeRuntime) -> None:
    fake_runtime.when("get pods", stdout="not json")
    payload = orchestrator.status(config, config.select([]))

    assert payload["available"] is False
    assert "unreadable" in payload["message"]


def test_down_deletes_only_pdd_managed_objects(config: DeploymentConfig, fake_runtime: FakeRuntime) -> None:
    fake_runtime.when("delete deployment,service", stdout='deployment.apps "api" deleted')
    outcomes = orchestrator.down(config, api(config))

    assert outcomes[0].ok is True
    assert fake_runtime.ran(
        "delete deployment,service",
        "--selector app.kubernetes.io/managed-by=pdd,app.kubernetes.io/name=api",
        "--ignore-not-found",
    )


def test_down_does_not_delete_the_cluster(config: DeploymentConfig, fake_runtime: FakeRuntime) -> None:
    orchestrator.down(config, api(config))
    assert not fake_runtime.ran("kind delete cluster")


def test_delete_cluster_targets_only_the_named_cluster(
    config: DeploymentConfig, fake_runtime: FakeRuntime
) -> None:
    step = orchestrator.delete_cluster(config)
    assert step.ok is True
    assert fake_runtime.ran("kind delete cluster --name demo-local")


def test_logs_are_scoped_to_one_service(config: DeploymentConfig, fake_runtime: FakeRuntime) -> None:
    fake_runtime.when("logs", stdout="[api-1] listening on 8000\n")
    text, error = orchestrator.logs(config, api(config)[0], tail=50)

    assert error is None
    assert "listening on 8000" in text
    assert fake_runtime.ran("logs", "--tail 50", "app.kubernetes.io/name=api")


def test_logs_failure_is_returned_not_raised(config: DeploymentConfig, fake_runtime: FakeRuntime) -> None:
    fake_runtime.when("logs", returncode=1, stderr="no pods found")
    text, error = orchestrator.logs(config, api(config)[0])

    assert text == ""
    assert error == "no pods found"


def test_zero_replica_service_skips_the_readiness_wait(
    config: DeploymentConfig, fake_runtime: FakeRuntime
) -> None:
    scaled = config.services["api"].model_copy(update={"replicas": 0})
    orchestrator.up(config, [scaled])
    assert not fake_runtime.ran("rollout status")
