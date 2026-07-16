import json
import re
import subprocess
import tomllib
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
def _template_variables(template_name: str) -> dict:
    template_path = REPO_ROOT / "ci" / "cloud-batch" / template_name
    data = json.loads(template_path.read_text(encoding="utf-8"))
    runnable = data["taskGroups"][0]["taskSpec"]["runnables"][0]
    return runnable["environment"]


def _template_container(template_name: str) -> dict:
    template_path = REPO_ROOT / "ci" / "cloud-batch" / template_name
    data = json.loads(template_path.read_text(encoding="utf-8"))
    return data["taskGroups"][0]["taskSpec"]["runnables"][0]["container"]


def _template_task_indexes(template_name: str) -> list[int]:
    """Return the global result indexes produced by one Batch template."""
    template_path = REPO_ROOT / "ci" / "cloud-batch" / template_name
    data = json.loads(template_path.read_text(encoding="utf-8"))
    group = data["taskGroups"][0]
    variables = group["taskSpec"]["runnables"][0]["environment"]["variables"]

    if "FIXED_TASK_INDEX" in variables:
        return [int(variables["FIXED_TASK_INDEX"])]

    offset = int(variables.get("TASK_INDEX_OFFSET", "0"))
    skipped = [
        int(value)
        for value in variables.get("SKIP_INDEXES", "").split(",")
        if value
    ]
    logical_cases = variables.get("CLOUD_REGRESSION_CASES")
    if logical_cases:
        return [
            int(variables.get("TASK_INDEX_OFFSET", "0")) + int(case) - 1
            for case in logical_cases.split(",")
        ]
    indexes = []
    for raw_index in range(int(group["taskCount"])):
        task_index = raw_index + offset
        for skipped_index in skipped:
            if skipped_index <= task_index:
                task_index += 1
        indexes.append(task_index)
    return indexes


def _setup_secret_names() -> set[str]:
    setup_path = REPO_ROOT / "ci" / "cloud-batch" / "setup-gcp.sh"
    setup_text = setup_path.read_text(encoding="utf-8")
    secrets_block = re.search(r"SECRETS=\((.*?)\)", setup_text, re.DOTALL)
    assert secrets_block, "setup-gcp.sh must define a SECRETS array"
    return set(re.findall(r'"([^"]+)"', secrets_block.group(1)))


def test_cloud_batch_templates_route_cloud_regression_to_staging():
    for template_name in (
        "job-template-pytest.json",
        "job-template.json",
        "job-template-standard.json",
        "job-template-cloud-regression.json",
    ):
        environment = _template_variables(template_name)
        variables = environment["variables"]

        assert (
            variables["PDD_CLOUD_URL"]
            == "https://{{REGION}}-{{PROJECT_ID}}.cloudfunctions.net"
        )
        assert variables["PDD_ENV"] == "staging"
        assert variables["PDD_CLOUD_TIMEOUT"] == "1200"
        assert (
            variables["FIREBASE_API_KEY_SECRET_RESOURCE"]
            == "{{FIREBASE_API_KEY_SECRET_RESOURCE}}"
        )
        assert "secretVariables" not in environment


def test_cloud_batch_template_secrets_are_provisioned_by_setup_script():
    setup_secrets = _setup_secret_names()

    for template_name in (
        "job-template-pytest.json",
        "job-template.json",
        "job-template-standard.json",
        "job-template-cloud-regression.json",
    ):
        environment = _template_variables(template_name)
        secret_keys = {
            key
            for key, value in environment["variables"].items()
            if key.endswith("_SECRET_RESOURCE")
        }
        expected_secret_names = {
            "GCS_HMAC_ACCESS_KEY_ID_SECRET_RESOURCE": "GCS_HMAC_ACCESS_KEY_ID",
            "GCS_HMAC_SECRET_ACCESS_KEY_SECRET_RESOURCE": "GCS_HMAC_SECRET_ACCESS_KEY",
            "OPENAI_API_KEY_SECRET_RESOURCE": "OPENAI_API_KEY",
            "FIREBASE_API_KEY_SECRET_RESOURCE": "staging-firebase-api-key",
            "GITHUB_CLIENT_ID_SECRET_RESOURCE": "github-client-id",
            "PDD_REFRESH_TOKEN_SECRET_RESOURCE": "pdd-refresh-token",
            "CLAUDE_CODE_OAUTH_TOKEN_SECRET_RESOURCE": "CLAUDE_CODE_OAUTH_TOKEN",
        }
        assert secret_keys == set(expected_secret_names)
        template_secrets = {expected_secret_names[key] for key in secret_keys}

        assert template_secrets <= setup_secrets


def test_spot_template_provisioning_model_is_release_gate_overridable():
    for template_name in ("job-template-pytest.json", "job-template.json"):
        spot_template_path = REPO_ROOT / "ci" / "cloud-batch" / template_name
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

    assert spot_group["taskCount"] == "36"
    assert spot_group["parallelism"] == "36"
    assert spot_vars["TASK_INDEX_OFFSET"] == "32"
    assert spot_vars["SKIP_INDEXES"] == "54,68,69,70,71,72,73,74,75"

    cloud_template_path = (
        REPO_ROOT / "ci" / "cloud-batch" / "job-template-cloud-regression.json"
    )
    cloud_template = json.loads(cloud_template_path.read_text(encoding="utf-8"))
    cloud_group = cloud_template["taskGroups"][0]
    cloud_policy = cloud_template["allocationPolicy"]["instances"][0]["policy"]
    cloud_vars = cloud_group["taskSpec"]["runnables"][0]["environment"]["variables"]

    assert cloud_group["taskCount"] == "1"
    assert cloud_group["parallelism"] == "1"
    assert cloud_vars["TASK_INDEX_OFFSET"] == "68"
    assert cloud_vars["CLOUD_REGRESSION_CASES"] == "1,2,3,4,5,6,7,8"
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

    assert "useradd --create-home" in dockerfile_text
    assert "pdd ALL=(ALL) NOPASSWD: ALL" in dockerfile_text


def test_cloud_batch_pytest_runs_as_non_root_sandbox_user():
    entrypoint_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "entrypoint.sh"
    ).read_text(encoding="utf-8")

    assert 'PYTEST_SANDBOX_USER="pdd"' in entrypoint_text
    assert "chown -R pdd:pdd" in entrypoint_text
    assert '"${PYTEST_USER_COMMAND[@]}" sudo -n true' in entrypoint_text
    assert '"${PYTEST_USER_COMMAND[@]}" python -m pytest' in entrypoint_text


def test_cloud_batch_entrypoint_preflights_protected_sandbox_contract():
    entrypoint_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "entrypoint.sh"
    ).read_text(encoding="utf-8")

    assert "for command in bwrap sudo setpriv mount umount" in entrypoint_text
    assert "sudo -n true" in entrypoint_text
    assert "missing protected sandbox prerequisites" in entrypoint_text


def test_only_pytest_shard_job_grants_required_sandbox_privilege():
    pytest_container = _template_container("job-template-pytest.json")
    assert pytest_container["options"] == "--privileged"
    assert "--cap-add=SYS_ADMIN --security-opt=seccomp=unconfined" not in (
        pytest_container["options"]
    )

    for template_name in (
        "job-template.json",
        "job-template-standard.json",
        "job-template-cloud-regression.json",
    ):
        container = _template_container(template_name)
        assert "options" not in container
        assert "--privileged" not in json.dumps(container)


def test_cloud_batch_templates_partition_all_result_indexes_exactly_once():
    pytest_indexes = _template_task_indexes("job-template-pytest.json")
    regression_indexes = _template_task_indexes("job-template.json")
    slow_sync_indexes = _template_task_indexes("job-template-standard.json")
    cloud_indexes = _template_task_indexes("job-template-cloud-regression.json")

    assert pytest_indexes == list(range(0, 32))
    assert regression_indexes == [
        *range(32, 54),
        *range(55, 68),
        76,
    ]
    assert slow_sync_indexes == [54]
    assert cloud_indexes == list(range(68, 76))

    all_indexes = [
        *pytest_indexes,
        *regression_indexes,
        *slow_sync_indexes,
        *cloud_indexes,
    ]
    assert len(all_indexes) == 77
    assert sorted(all_indexes) == list(range(77))


def test_cloud_regression_uses_one_physical_task_for_eight_logical_results():
    template = json.loads(
        (REPO_ROOT / "ci" / "cloud-batch" / "job-template-cloud-regression.json").read_text(
            encoding="utf-8"
        )
    )
    group = template["taskGroups"][0]
    variables = group["taskSpec"]["runnables"][0]["environment"]["variables"]

    assert group["taskCount"] == "1"
    assert group["parallelism"] == "1"
    assert variables["TASK_INDEX_OFFSET"] == "68"
    assert variables["CLOUD_REGRESSION_CASES"] == "1,2,3,4,5,6,7,8"

    submit = (REPO_ROOT / "ci" / "cloud-batch" / "submit.sh").read_text(
        encoding="utf-8"
    )
    assert '_validate_rendered_template /tmp/pdd-batch-job-cloud.json 1' in submit
    assert '--job-spec "${JOB_NAME_CLOUD}=${JOB_UID_CLOUD}=1"' in submit
    assert '"physical_task_indexes": [0] * 8' in submit
    assert "PHYSICAL_TOTAL=70" in submit
    assert "LOGICAL_TOTAL=77" in submit
    collector = (REPO_ROOT / "ci" / "cloud-batch" / "collect-results.sh").read_text(
        encoding="utf-8"
    )
    assert 'LOGICAL_TOTAL=$(python3 - "${EVIDENCE_FILE}"' in collector
    assert "indexes != list(range(77))" in collector
    assert 'TOTAL="${LOGICAL_TOTAL}"' in collector

    submit_text = (REPO_ROOT / "ci" / "cloud-batch" / "submit.sh").read_text(
        encoding="utf-8"
    )
    for template_name in (
        "job-template-pytest.json",
        "job-template.json",
        "job-template-standard.json",
        "job-template-cloud-regression.json",
    ):
        assert template_name in submit_text
    for job_variable in (
        "JOB_NAME_PYTEST",
        "JOB_NAME_MAIN",
        "JOB_NAME_STD",
        "JOB_NAME_CLOUD",
    ):
        assert f'_job_status "${{{job_variable}}}"' in submit_text
        assert f'"${{{job_variable}}}"' in submit_text


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


def test_cloud_batch_entrypoint_verifies_exact_git_candidate_before_install():
    entrypoint = REPO_ROOT / "ci" / "cloud-batch" / "entrypoint.sh"
    entrypoint_text = entrypoint.read_text(encoding="utf-8")
    verify = 'python3 /source-identity.py verify --work-dir "${WORK_DIR}"'
    assert verify in entrypoint_text
    assert "initialize_source_git_snapshot" not in entrypoint_text
    assert entrypoint_text.index(verify) < (
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
    source_identity = (
        REPO_ROOT / "ci" / "cloud-batch" / "source-identity.py"
    ).read_text(encoding="utf-8")
    assert "SOURCE_PATHS" not in submit_text
    assert '"ls-tree",' in source_identity
    assert '"cat-file", "--batch"' in source_identity


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


def test_cloud_batch_attempt_evidence_is_collected_and_secret_scanned():
    submit = (REPO_ROOT / "ci" / "cloud-batch" / "submit.sh").read_text(
        encoding="utf-8"
    )
    collector = (REPO_ROOT / "ci" / "cloud-batch" / "collect-results.sh").read_text(
        encoding="utf-8"
    )

    assert "results/cloud_regression_attempt_*.jsonl" in submit
    assert '"${STREAMING_DIR}"/cloud_regression_attempt_*.jsonl' in submit
    assert 'cloud_regression_attempt_*.jsonl "${RESULTS_LOCAL}/"' in collector


def test_serial_cloud_regression_has_coherent_aggregate_runtime_budget():
    template = json.loads(
        (REPO_ROOT / "ci" / "cloud-batch" / "job-template-cloud-regression.json")
        .read_text(encoding="utf-8")
    )
    task_seconds = int(
        template["taskGroups"][0]["taskSpec"]["maxRunDuration"].removesuffix("s")
    )
    max_retry_count = template["taskGroups"][0]["taskSpec"]["maxRetryCount"]
    submit = (REPO_ROOT / "ci" / "cloud-batch" / "submit.sh").read_text(
        encoding="utf-8"
    )
    poll_seconds = int(re.search(r'POLL_TIMEOUT="\$\{POLL_TIMEOUT:-(\d+)\}"', submit).group(1))

    assert task_seconds >= 8 * 1200 + 1800
    assert poll_seconds >= task_seconds * (max_retry_count + 1) + 1200


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
    entrypoint_path = REPO_ROOT / "ci" / "cloud-batch" / "entrypoint.sh"
    entrypoint_text = entrypoint_path.read_text(encoding="utf-8")

    assert "TASK_INDEX_OFFSET" in entrypoint_text
    assert "SKIP_INDEXES" in entrypoint_text
    assert 'IFS=\',\' read -r -a _SKIP_INDEXES' in entrypoint_text

    mapping_script = entrypoint_text.split('RESULTS_DIR="/mnt/disks/results"', 1)[0]
    mapping_script += '\nprintf "%s\\n" "${TASK_INDEX}"\n'
    skipped = "54,68,69,70,71,72,73,74,75"
    cases = (
        ({"BATCH_TASK_INDEX": "31"}, "31"),
        ({"BATCH_TASK_INDEX": "0", "TASK_INDEX_OFFSET": "32", "SKIP_INDEXES": skipped}, "32"),
        ({"BATCH_TASK_INDEX": "21", "TASK_INDEX_OFFSET": "32", "SKIP_INDEXES": skipped}, "53"),
        ({"BATCH_TASK_INDEX": "22", "TASK_INDEX_OFFSET": "32", "SKIP_INDEXES": skipped}, "55"),
        ({"BATCH_TASK_INDEX": "35", "TASK_INDEX_OFFSET": "32", "SKIP_INDEXES": skipped}, "76"),
        ({"BATCH_TASK_INDEX": "0", "FIXED_TASK_INDEX": "54"}, "54"),
        ({"BATCH_TASK_INDEX": "7", "TASK_INDEX_OFFSET": "68"}, "75"),
    )

    for environment, expected in cases:
        result = subprocess.run(
            ["bash", "-c", mapping_script],
            check=True,
            text=True,
            capture_output=True,
            env=environment,
        )
        assert result.stdout.strip() == expected
