import sys
sys.path.insert(0, '/tmp/pdd_job_LpFrqbS7pZ0P37hf4AUP_agw_as0q')
from unittest.mock import patch, MagicMock
from pathlib import Path
import json
from pdd.agentic_checkup import run_agentic_checkup

issue_data = {
    "title": "Check {workflow}",
    "body": "check {value}",
    "comments_url": "",
}

with patch("pdd.checkup_review_loop.run_checkup_review_loop") as mock_review_loop, \
     patch("pdd.agentic_checkup._fetch_pr_context", return_value='PR context {"ok": true}'), \
     patch("pdd.agentic_checkup._load_pddrc_content", return_value="setting: {raw}"), \
     patch("pdd.agentic_checkup._load_architecture_json", return_value=([{"name": "{module}"}], Path("/tmp/arch.json"))), \
     patch("pdd.agentic_checkup.find_project_root", return_value=Path("/tmp/project")), \
     patch("pdd.agentic_checkup._gh_api") as mock_run_cmd, \
     patch("pdd.agentic_checkup._check_gh_cli", return_value=True):
    
    mock_run_cmd.return_value = (True, json.dumps(issue_data), "")
    mock_review_loop.return_value = (True, "review report", 0.10, "codex")

    try:
        run_agentic_checkup(
            "https://github.com/owner/repo/issues/1",
            quiet=False,
            pr_url="https://github.com/owner/repo/pull/2",
            review_loop=True,
            review_only=True,
            use_github_state=False
        )
    except Exception as e:
        import traceback
        traceback.print_exc()

