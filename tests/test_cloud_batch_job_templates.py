import json
import re
import subprocess
import tomllib
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SECRET_PATH_PATTERN = re.compile(r"/secrets/([^/]+)/versions/latest")


def _template_variables(template_name: str) -> dict:
    template_path = REPO_ROOT / "ci" / "cloud-batch" / template_name
    data = json.loads(template_path.read_text(encoding="utf-8"))
    runnable = data["taskGroups"][0]["taskSpec"]["runnables"][0]
    return runnable["environment"]


def _template_container(template_name: str) -> dict:
    template_path = REPO_ROOT / "ci" / "cloud-batch" / template_name
    data = json.loads(template_path.read_text(encoding="utf-8"))
    return data["taskGroups"][0]["taskSpec"]["runnables"][0]["container"]


def _setup_secret_names() -> set[str]:
    setup_path = REPO_ROOT / "ci" / "cloud-batch" / "setup-gcp.sh"
    setup_text = setup_path.read_text(encoding="utf-8")
    secrets_block = re.search(r"SECRETS=\((.*?)\)", setup_text, re.DOTALL)
    assert secrets_block, "setup-gcp.sh must define a SECRETS array"
    return set(re.findall(r'"([^"]+)"', secrets_block.group(1)))


def test_cloud_batch_templates_route_cloud_regression_to_staging():
    for template_name in (
        "job-template.json",
        "job-template-standard.json",
        "job-template-cloud-regression.json",
    ):
        environment = _template_variables(template_name)
        variables = environment["variables"]
        secrets = environment["secretVariables"]

        assert (
            variables["PDD_CLOUD_URL"]
            == "https://{{REGION}}-{{PROJECT_ID}}.cloudfunctions.net"
        )
        assert variables["PDD_ENV"] == "staging"
        assert variables["PDD_CLOUD_TIMEOUT"] == "1200"
        assert (
            secrets["FIREBASE_API_KEY"]
            == "projects/{{PROJECT_ID}}/secrets/staging-firebase-api-key/versions/latest"
        )


def test_cloud_batch_template_secrets_are_provisioned_by_setup_script():
    setup_secrets = _setup_secret_names()

    for template_name in (
        "job-template.json",
        "job-template-standard.json",
        "job-template-cloud-regression.json",
    ):
        environment = _template_variables(template_name)
        secret_paths = environment["secretVariables"].values()
        template_secrets = {
            match.group(1)
            for secret_path in secret_paths
            if (match := SECRET_PATH_PATTERN.search(secret_path))
        }

        assert template_secrets <= setup_secrets


def test_spot_template_provisioning_model_is_release_gate_overridable():
    spot_template_path = REPO_ROOT / "ci" / "cloud-batch" / "job-template.json"
    spot_template = json.loads(spot_template_path.read_text(encoding="utf-8"))
    spot_policy = spot_template["allocationPolicy"]["instances"][0]["policy"]
    assert spot_policy["provisioningModel"] == "{{SPOT_PROVISIONING_MODEL}}"

    standard_template_path = (
        REPO_ROOT / "ci" / "cloud-batch" / "job-template-standard.json"
    )
    standard_template = json.loads(standard_template_path.read_text(encoding="utf-8"))
    standard_policy = standard_template["allocationPolicy"]["instances"][0]["policy"]
    assert standard_policy["provisioningModel"] == "STANDARD"

    submit_text = (REPO_ROOT / "ci" / "cloud-batch" / "submit.sh").read_text(
        encoding="utf-8"
    )
    assert "PDD_CLOUD_BATCH_SPOT_PROVISIONING_MODEL" in submit_text
    assert "{{SPOT_PROVISIONING_MODEL}}" in submit_text


def test_cloud_batch_runs_cloud_regression_serially():
    spot_template_path = REPO_ROOT / "ci" / "cloud-batch" / "job-template.json"
    spot_template = json.loads(spot_template_path.read_text(encoding="utf-8"))
    spot_group = spot_template["taskGroups"][0]
    spot_vars = spot_group["taskSpec"]["runnables"][0]["environment"]["variables"]

    assert spot_group["taskCount"] == "68"
    assert spot_group["parallelism"] == "68"
    assert spot_vars["SKIP_INDEXES"] == "54,68,69,70,71,72,73,74,75"

    cloud_template_path = (
        REPO_ROOT / "ci" / "cloud-batch" / "job-template-cloud-regression.json"
    )
    cloud_template = json.loads(cloud_template_path.read_text(encoding="utf-8"))
    cloud_group = cloud_template["taskGroups"][0]
    cloud_policy = cloud_template["allocationPolicy"]["instances"][0]["policy"]
    cloud_vars = cloud_group["taskSpec"]["runnables"][0]["environment"]["variables"]

    assert cloud_group["taskCount"] == "8"
    assert cloud_group["parallelism"] == "1"
    assert cloud_vars["TASK_INDEX_OFFSET"] == "68"
    assert cloud_policy["provisioningModel"] == "STANDARD"

    submit_text = (REPO_ROOT / "ci" / "cloud-batch" / "submit.sh").read_text(
        encoding="utf-8"
    )
    assert "job-template-cloud-regression.json" in submit_text
    assert "JOB_NAME_CLOUD" in submit_text


def test_cloud_batch_image_installs_and_verifies_github_cli():
    dockerfile_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "Dockerfile"
    ).read_text(encoding="utf-8")
    cloudbuild_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "cloudbuild.yaml"
    ).read_text(encoding="utf-8")

    assert re.search(r"^\s*gh\s*\\$", dockerfile_text, re.MULTILINE)
    assert '"gh"' in cloudbuild_text
    assert "gh --version" in cloudbuild_text or '["gh", "--version"]' in cloudbuild_text


def test_cloud_batch_image_provisions_protected_linux_sandbox():
    dockerfile_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "Dockerfile"
    ).read_text(encoding="utf-8")

    for package in ("bubblewrap", "sudo", "util-linux"):
        assert re.search(
            rf"^\s*{re.escape(package)}\s*\\$", dockerfile_text, re.MULTILINE
        ), f"Cloud Batch image must install {package}"


def test_cloud_batch_entrypoint_preflights_protected_sandbox_contract():
    entrypoint_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "entrypoint.sh"
    ).read_text(encoding="utf-8")

    assert "for command in bwrap sudo setpriv mount umount" in entrypoint_text
    assert "sudo -n true" in entrypoint_text
    assert "missing protected sandbox prerequisites" in entrypoint_text


def test_only_pytest_shard_job_grants_minimal_sandbox_capabilities():
    pytest_container = _template_container("job-template.json")
    assert pytest_container["options"] == (
        "--cap-add=SYS_ADMIN --security-opt=seccomp=unconfined"
    )
    assert "--privileged" not in pytest_container["options"]

    for template_name in (
        "job-template-standard.json",
        "job-template-cloud-regression.json",
    ):
        container = _template_container(template_name)
        assert "options" not in container
        assert "--privileged" not in json.dumps(container)


def test_cloud_batch_sandbox_preflight_is_scoped_to_pytest_task_indexes():
    entrypoint_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "entrypoint.sh"
    ).read_text(encoding="utf-8")

    assert "preflight_protected_sandbox()" in entrypoint_text
    assert re.search(
        r'if \[ "\$\{TASK_INDEX\}" -ge "\$\{PYTEST_START\}" \] &&\s*'
        r'\[ "\$\{TASK_INDEX\}" -le "\$\{PYTEST_END\}" \]; then\s*'
        r'preflight_protected_sandbox\s*fi',
        entrypoint_text,
    )


def test_cloud_batch_entrypoint_builds_clean_ephemeral_git_head(tmp_path):
    entrypoint = REPO_ROOT / "ci" / "cloud-batch" / "entrypoint.sh"
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    (workspace / ".gitignore").write_text("*.egg-info/\n", encoding="utf-8")
    (workspace / "payload.py").write_text("VALUE = 1\n", encoding="utf-8")
    ignored_upload = workspace / "tracked.egg-info" / "PKG-INFO"
    ignored_upload.parent.mkdir()
    ignored_upload.write_text("uploaded tracked bytes\n", encoding="utf-8")
    (workspace / ".pdd-package-version").write_text("0.0.303.dev1\n", encoding="utf-8")
    (workspace / ".pddrc_pddcloud").write_text("[pdd]\n", encoding="utf-8")

    script = f"""
set -euo pipefail
source <(sed -n '/^initialize_source_git_snapshot() {{/,/^}}/p' {entrypoint!s})
WORK_DIR={workspace!s}
initialize_source_git_snapshot
"""
    subprocess.run(["bash", "-c", script], check=True, text=True, capture_output=True)

    head = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"], cwd=workspace,
        check=True, text=True, capture_output=True,
    ).stdout.strip()
    status = subprocess.run(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"],
        cwd=workspace, check=True, text=True, capture_output=True,
    ).stdout
    tracked = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", head], cwd=workspace,
        check=True, text=True, capture_output=True,
    ).stdout.splitlines()

    assert status == ""
    assert {".gitignore", "payload.py", "tracked.egg-info/PKG-INFO"} <= set(tracked)
    assert ".pdd-package-version" not in tracked
    assert ".pddrc_pddcloud" not in tracked
    assert (workspace / ".pdd-package-version").read_text() == "0.0.303.dev1\n"
    assert (workspace / ".pddrc_pddcloud").read_text() == "[pdd]\n"

    entrypoint_text = entrypoint.read_text(encoding="utf-8")
    assert entrypoint_text.index("initialize_source_git_snapshot\n") < (
        entrypoint_text.index('pip install -e ".[dev]"')
    )


def test_cloud_batch_uploaded_pyproject_registers_story_marker():
    pyproject = tomllib.loads(
        (REPO_ROOT / "pyproject.toml").read_text(encoding="utf-8")
    )
    markers = pyproject["tool"]["pytest"]["ini_options"]["markers"]

    assert any(marker.startswith("story(") for marker in markers)


def test_cloud_batch_uploaded_source_includes_story_artifacts():
    submit_text = (REPO_ROOT / "ci" / "cloud-batch" / "submit.sh").read_text(
        encoding="utf-8"
    )
    source_paths = re.search(r"SOURCE_PATHS=\((.*?)\)", submit_text, re.DOTALL)
    assert source_paths, "submit.sh must define SOURCE_PATHS"

    assert re.search(r"^\s*user_stories\s*$", source_paths.group(1), re.MULTILINE)


def test_cloud_batch_entrypoint_scopes_jwt_exchange_to_cloud_regression():
    entrypoint_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "entrypoint.sh"
    ).read_text(encoding="utf-8")

    assert "NEEDS_PDD_JWT=0" in entrypoint_text
    assert "CLOUD_REGRESSION_START" in entrypoint_text
    assert "PDD_BATCH_ENABLE_PYTEST_CLOUD_E2E" in entrypoint_text
    assert "Skipping PDD JWT exchange" in entrypoint_text


def test_cloud_batch_entrypoint_extends_quota_retry_horizon():
    """Quota exhaustion must cool down longer than generic transient errors."""
    entrypoint_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "entrypoint.sh"
    ).read_text(encoding="utf-8")

    assert "JWT_MAX_ATTEMPTS=6" in entrypoint_text
    assert "JWT_QUOTA_BACKOFF_SECONDS=30" in entrypoint_text
    assert '"${JWT_ERROR}" = "QUOTA_EXCEEDED"' in entrypoint_text


def test_cloud_batch_entrypoint_forces_pytest_shards_local_by_default():
    entrypoint_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "entrypoint.sh"
    ).read_text(encoding="utf-8")
    pytest_branch = re.search(
        r'if \[ "\$\{TASK_INDEX\}" -ge "\$\{PYTEST_START\}" \].*?'
        r'CHUNK_INDEX="\$\{TASK_INDEX\}"',
        entrypoint_text,
        re.DOTALL,
    )

    assert pytest_branch, "entrypoint.sh must keep an explicit pytest shard branch"
    assert "PDD_FORCE_LOCAL=1" in pytest_branch.group(0)
    assert "unset PDD_JWT_TOKEN" in pytest_branch.group(0)


def test_cloud_batch_entrypoint_maps_skipped_and_offset_task_indexes():
    entrypoint_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "entrypoint.sh"
    ).read_text(encoding="utf-8")

    assert "TASK_INDEX_OFFSET" in entrypoint_text
    assert "SKIP_INDEXES" in entrypoint_text
    assert 'IFS=\',\' read -r -a _SKIP_INDEXES' in entrypoint_text
