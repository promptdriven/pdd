import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _template_variables(template_name: str) -> dict:
    template_path = REPO_ROOT / "ci" / "cloud-batch" / template_name
    data = json.loads(template_path.read_text(encoding="utf-8"))
    runnable = data["taskGroups"][0]["taskSpec"]["runnables"][0]
    return runnable["environment"]


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
