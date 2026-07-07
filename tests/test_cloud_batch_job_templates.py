import json
import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SECRET_PATH_PATTERN = re.compile(r"/secrets/([^/]+)/versions/latest")


def _template_variables(template_name: str) -> dict:
    template_path = REPO_ROOT / "ci" / "cloud-batch" / template_name
    data = json.loads(template_path.read_text(encoding="utf-8"))
    runnable = data["taskGroups"][0]["taskSpec"]["runnables"][0]
    return runnable["environment"]


def _setup_secret_names() -> set[str]:
    setup_path = REPO_ROOT / "ci" / "cloud-batch" / "setup-gcp.sh"
    setup_text = setup_path.read_text(encoding="utf-8")
    secrets_block = re.search(r"SECRETS=\((.*?)\)", setup_text, re.DOTALL)
    assert secrets_block, "setup-gcp.sh must define a SECRETS array"
    return set(re.findall(r'"([^"]+)"', secrets_block.group(1)))


def test_cloud_batch_templates_route_cloud_regression_to_staging():
    for template_name in ("job-template.json", "job-template-standard.json"):
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

    for template_name in ("job-template.json", "job-template-standard.json"):
        environment = _template_variables(template_name)
        secret_paths = environment["secretVariables"].values()
        template_secrets = {
            match.group(1)
            for secret_path in secret_paths
            if (match := SECRET_PATH_PATTERN.search(secret_path))
        }

        assert template_secrets <= setup_secrets
