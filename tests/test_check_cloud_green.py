"""Contract tests for the pre-release cloud gate check.

The release must consume a commit the cloud gate already proved green rather
than running the gate itself. These tests pin the refusal behaviour: an
unreadable, empty, stale, or mismatched gate history must all block the
release, because a gate that fails open is worse than no gate at all.
"""

from __future__ import annotations

import datetime
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "check_cloud_green.py"
WORKFLOW = ROOT / ".github" / "workflows" / "cloud-test-main.yml"
MAKEFILE = ROOT / "Makefile"

sys.path.insert(0, str(ROOT / "scripts"))

from check_cloud_green import (  # noqa: E402
    CloudGreenError,
    GreenRun,
    git_ancestor_check,
    newest_green_ancestor,
    parse_runs,
    select_green,
    validate_max_age,
)

NOW = datetime.datetime(2026, 7, 26, 12, 0, 0, tzinfo=datetime.timezone.utc)
CANDIDATE = "a" * 40
OTHER = "b" * 40


def run_payload(sha: str, hours_ago: float, url: str = "https://example/run") -> dict:
    """Build one `gh run list --json headSha,updatedAt,url` entry."""
    stamp = NOW - datetime.timedelta(hours=hours_ago)
    return {
        "headSha": sha,
        "updatedAt": stamp.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "url": url,
    }


class TestParseRuns:
    def test_parses_a_well_formed_history(self):
        runs = parse_runs(json.dumps([run_payload(CANDIDATE, 1.0)]))
        assert [run.head_sha for run in runs] == [CANDIDATE]
        assert runs[0].age_hours(NOW) == pytest.approx(1.0)

    def test_empty_history_is_a_refusal_not_an_empty_list(self):
        # gh printing nothing (auth failure, network error) must not read as
        # "no runs found" and certainly not as "green".
        with pytest.raises(CloudGreenError, match="empty"):
            parse_runs("   ")

    def test_malformed_json_is_a_refusal(self):
        with pytest.raises(CloudGreenError, match="not valid JSON"):
            parse_runs("{not json")

    def test_non_list_payload_is_a_refusal(self):
        with pytest.raises(CloudGreenError, match="not a JSON list"):
            parse_runs('{"headSha": "x"}')

    def test_missing_field_is_a_refusal(self):
        with pytest.raises(CloudGreenError, match="missing"):
            parse_runs('[{"headSha": "x", "url": "u"}]')

    def test_unparseable_timestamp_is_a_refusal(self):
        with pytest.raises(CloudGreenError, match="unparseable updatedAt"):
            parse_runs('[{"headSha": "x", "updatedAt": "never", "url": "u"}]')

    def test_naive_timestamp_is_treated_as_utc(self):
        runs = parse_runs('[{"headSha": "x", "updatedAt": "2026-07-26T11:00:00", "url": "u"}]')
        assert runs[0].age_hours(NOW) == pytest.approx(1.0)


class TestSelectGreen:
    def test_accepts_a_fresh_green_for_the_exact_candidate(self):
        runs = parse_runs(json.dumps([run_payload(CANDIDATE, 2.0)]))
        assert select_green(runs, CANDIDATE, 24.0, NOW).head_sha == CANDIDATE

    def test_refuses_when_no_run_matches_the_candidate(self):
        runs = parse_runs(json.dumps([run_payload(OTHER, 1.0)]))
        with pytest.raises(CloudGreenError) as excinfo:
            select_green(runs, CANDIDATE, 24.0, NOW)
        message = str(excinfo.value)
        # The refusal has to be actionable: it names the proven commits so the
        # operator can see whether the gate simply has not caught up yet.
        assert OTHER in message
        assert "PR loop" in message

    def test_refuses_an_empty_history(self):
        with pytest.raises(CloudGreenError, match="never gone green"):
            select_green([], CANDIDATE, 24.0, NOW)

    def test_refuses_a_stale_green(self):
        runs = parse_runs(json.dumps([run_payload(CANDIDATE, 30.0)]))
        with pytest.raises(CloudGreenError, match="30.0h old"):
            select_green(runs, CANDIDATE, 24.0, NOW)

    def test_refuses_a_future_dated_green(self):
        # Negative age means the local clock is behind the run timestamp. An
        # upper-bound-only check would make every green look arbitrarily fresh,
        # and a clock behind by more than the green's true age would pass
        # unconditionally.
        runs = parse_runs(json.dumps([run_payload(CANDIDATE, -87600.0)]))
        with pytest.raises(CloudGreenError, match="future"):
            select_green(runs, CANDIDATE, 24.0, NOW)

    def test_boundary_age_is_accepted(self):
        runs = parse_runs(json.dumps([run_payload(CANDIDATE, 24.0)]))
        assert select_green(runs, CANDIDATE, 24.0, NOW).head_sha == CANDIDATE

    def test_newest_proof_wins_when_a_sha_was_run_twice(self):
        # A re-run or a scheduled run on unchanged main both produce duplicate
        # SHAs; the stale one must not veto the fresh one.
        runs = parse_runs(
            json.dumps(
                [
                    run_payload(CANDIDATE, 40.0, "https://example/old"),
                    run_payload(CANDIDATE, 1.0, "https://example/new"),
                ]
            )
        )
        assert select_green(runs, CANDIDATE, 24.0, NOW).url == "https://example/new"


class TestAncestorSuggestion:
    """A refusal must name the newest proven ancestor, not just say no.

    The gate still matches HEAD exactly — that is what keeps the tagged commit
    and the validated commit identical. But main moves every ~7 minutes while
    the gate takes ~2h, so HEAD is rarely blessed. Without a suggested ancestor
    the gate deadlocks releases and operators route around it.
    """

    def test_picks_the_newest_fresh_ancestor(self):
        runs = parse_runs(
            json.dumps(
                [
                    run_payload("c" * 40, 1.0, "https://example/not-ancestor"),
                    run_payload("a" * 40, 3.0, "https://example/older-ancestor"),
                    run_payload("b" * 40, 2.0, "https://example/newer-ancestor"),
                ]
            )
        )
        ancestors = {"a" * 40, "b" * 40}
        best = newest_green_ancestor(runs, lambda sha: sha in ancestors, 24.0, NOW)
        assert best is not None
        assert best.url == "https://example/newer-ancestor"

    def test_ignores_greens_that_are_not_ancestors(self):
        # A green on a branch or a force-pushed commit is not releasable.
        runs = parse_runs(json.dumps([run_payload(OTHER, 1.0)]))
        assert newest_green_ancestor(runs, lambda sha: False, 24.0, NOW) is None

    def test_ignores_stale_and_future_dated_ancestors(self):
        runs = parse_runs(
            json.dumps([run_payload("a" * 40, 99.0), run_payload("b" * 40, -5.0)])
        )
        assert newest_green_ancestor(runs, lambda sha: True, 24.0, NOW) is None

    def test_unresolvable_sha_is_not_treated_as_an_ancestor(self, tmp_path):
        # git_ancestor_check must return False, not raise, for a SHA git cannot
        # resolve — an unknown commit is not proven history.
        subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
        predicate = git_ancestor_check("HEAD")
        cwd = os.getcwd()
        try:
            os.chdir(tmp_path)
            assert predicate("f" * 40) is False
        finally:
            os.chdir(cwd)

    def test_script_prints_an_actionable_checkout_on_refusal(self, tmp_path):
        # Build a tiny real repo so the ancestor predicate runs against git.
        def git(*args):
            subprocess.run(["git", *args], cwd=tmp_path, check=True,
                           capture_output=True)

        git("init", "-q", "-b", "main")
        git("config", "user.email", "t@example.com")
        git("config", "user.name", "t")
        (tmp_path / "f").write_text("1", encoding="utf8")
        git("add", "f")
        git("commit", "-qm", "first")
        proven = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                                capture_output=True, text=True, check=True).stdout.strip()
        (tmp_path / "f").write_text("2", encoding="utf8")
        git("add", "f")
        git("commit", "-qm", "second")
        tip = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                             capture_output=True, text=True, check=True).stdout.strip()

        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--candidate-sha", tip,
             "--max-age-hours", "24", "--suggest-ancestor-of", "main"],
            input=json.dumps([run_payload(proven, 2.0)]),
            cwd=tmp_path,
            capture_output=True,
            text=True,
            check=False,
        )
        assert result.returncode == 1
        assert "Newest proven ancestor" in result.stderr
        assert proven in result.stderr
        assert f"git checkout --detach {proven}" in result.stderr


class TestReleaseAcceptsAProvenAncestor:
    def test_branch_check_requires_containment_not_equality(self):
        text = MAKEFILE.read_text(encoding="utf8")
        start = text.index("check-release-branch:")
        end = text.index("check-release-clean:", start)
        recipe = text[start:end]
        assert "merge-base --is-ancestor" in recipe
        # The old equality rule deadlocked the gate.
        assert 'if [ "$$LOCAL" != "$$REMOTE" ]' not in recipe

    def test_release_still_tags_head(self):
        # The tagged commit must remain the validated commit. Tagging anything
        # other than HEAD reintroduces the validate-one/ship-another hole.
        text = MAKEFILE.read_text(encoding="utf8")
        start = text.index("check-release-cloud-green:")
        end = text.index("check-release-video-config:", start)
        assert 'CANDIDATE_SHA="$$(git rev-parse HEAD)"' in text[start:end]


class TestFreshnessBoundCannotBeDisabled:
    """`inf`/`nan`/non-positive bounds must not silently retire the check."""

    @pytest.mark.parametrize("bad", (float("inf"), float("nan"), 0.0, -1.0))
    def test_rejects_bounds_that_disable_or_never_satisfy(self, bad):
        with pytest.raises(CloudGreenError):
            validate_max_age(bad)

    def test_accepts_an_ordinary_bound(self):
        assert validate_max_age(24.0) == 24.0

    @pytest.mark.parametrize("bad", ("inf", "nan", "0", "-5"))
    def test_script_exits_nonzero_for_such_bounds(self, bad):
        # nan is the dangerous one: every comparison against it is False, so an
        # upper-bound test alone would pass a green of any age.
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--candidate-sha", CANDIDATE,
             "--max-age-hours", bad],
            input=json.dumps([run_payload(CANDIDATE, 8760.0)]),
            capture_output=True,
            text=True,
            check=False,
        )
        assert result.returncode == 1, result.stdout
        assert "Error:" in result.stderr

    def test_makefile_pins_the_bound_against_the_environment(self):
        # `?=` would let an exported var (e.g. a stray .envrc line, since this
        # repo uses direnv) win silently.
        text = MAKEFILE.read_text(encoding="utf8")
        assert "CLOUD_GREEN_MAX_AGE_HOURS := 24" in text
        assert "CLOUD_GREEN_MAX_AGE_HOURS ?=" not in text

    def test_gate_queries_the_canonical_repo(self):
        # gh prefers a remote named `upstream` over `origin`; check-release-remote
        # only validates origin, so run history could come from another repo.
        text = MAKEFILE.read_text(encoding="utf8")
        assert "--repo" in text
        assert "promptdriven/pdd" in text


class TestScriptInvocation:
    def _run(self, payload: str, sha: str = CANDIDATE, max_age: str = "24"):
        return subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--candidate-sha",
                sha,
                "--max-age-hours",
                max_age,
            ],
            input=payload,
            capture_output=True,
            text=True,
            check=False,
        )

    def test_exits_zero_and_reports_the_green(self):
        result = self._run(json.dumps([run_payload(CANDIDATE, 1.0)]))
        assert result.returncode == 0, result.stderr
        assert "Cloud gate green" in result.stdout
        assert CANDIDATE in result.stdout

    def test_exits_nonzero_on_refusal(self):
        result = self._run(json.dumps([run_payload(OTHER, 1.0)]))
        assert result.returncode == 1
        assert "Error:" in result.stderr

    def test_exits_nonzero_when_gh_produced_nothing(self):
        # The Makefile pipes gh straight into this script, so a failed gh call
        # arrives as empty stdin. That must block, not pass.
        result = self._run("")
        assert result.returncode == 1
        assert "Error:" in result.stderr


class TestReleaseWiring:
    def test_release_target_depends_on_the_cloud_gate(self):
        text = MAKEFILE.read_text(encoding="utf8")
        release_line = next(
            line for line in text.splitlines() if line.startswith("release:")
        )
        assert "check-release-cloud-green-gate" in release_line

    def test_gate_ships_disarmed_and_says_so(self):
        """Arming before the GCP service account exists blocks every release.

        No cloud-test-main run can exist until that account is provisioned, so
        a hard prerequisite would refuse every candidate. It ships disarmed and
        warns instead; arming is a one-line change.
        """
        text = MAKEFILE.read_text(encoding="utf8")
        assert "CLOUD_GREEN_GATE_ARMED := 0" in text
        start = text.index("check-release-cloud-green-gate:")
        end = text.index("check-release-cloud-green:", start)
        recipe = text[start:end]
        assert "NOT ARMED" in recipe
        assert "CLOUD_GREEN_GATE_ARMED" in recipe

    def test_arming_delegates_to_the_real_check(self):
        # Armed mode must run the genuine gate, not a weakened copy.
        text = MAKEFILE.read_text(encoding="utf8")
        start = text.index("check-release-cloud-green-gate:")
        end = text.index("check-release-cloud-green:", start)
        recipe = text[start:end]
        assert 'if [ "$(CLOUD_GREEN_GATE_ARMED)" = "1" ]' in recipe
        assert "check-release-cloud-green" in recipe

    def test_cloud_gate_target_is_phony(self):
        # The Makefile declares .PHONY across several lines; the target only
        # needs to appear in one of them.
        text = MAKEFILE.read_text(encoding="utf8")
        phony = " ".join(
            line for line in text.splitlines() if line.startswith(".PHONY:")
        )
        assert "check-release-cloud-green" in phony

    def test_gate_target_invokes_the_tested_script(self):
        text = MAKEFILE.read_text(encoding="utf8")
        assert "scripts/check_cloud_green.py" in text

    def test_gate_validates_head_with_no_sha_override(self):
        """The checked SHA must be the one that ships.

        `release` tags HEAD. An override steering this check at a different
        commit would let the gate bless one commit while another shipped —
        make exports command-line variables into recipe shells, so such a knob
        is reachable as `make release SOMEVAR=...`.
        """
        text = MAKEFILE.read_text(encoding="utf8")
        start = text.index("check-release-cloud-green:")
        end = text.index("check-release-video-config:", start)
        recipe = text[start:end]

        assert 'CANDIDATE_SHA="$$(git rev-parse HEAD)"' in recipe
        assert "RELEASE_SHA" not in recipe


class TestContinuousGateWorkflow:
    def test_workflow_exists_and_runs_the_same_gate_as_the_release(self):
        text = WORKFLOW.read_text(encoding="utf8")
        assert "make cloud-test" in text

    def test_workflow_is_timer_driven_not_push_driven(self):
        yaml = pytest.importorskip("yaml")
        spec = yaml.safe_load(WORKFLOW.read_text(encoding="utf8"))
        # PyYAML parses the bare `on:` key as the boolean True.
        triggers = spec[True] if True in spec else spec["on"]
        assert triggers["schedule"], "drift with no commit behind it needs a timer"
        assert "workflow_dispatch" in triggers
        # A push trigger cannot work here: the gate takes ~2h and main receives
        # a commit every ~7 minutes, so per-push runs only pile up.
        assert "push" not in triggers

    def test_workflow_never_cancels_a_run_in_flight(self):
        # submit.sh has no `gcloud batch jobs delete` on any path, so cancelling
        # the runner abandons 77 Cloud Batch tasks rather than stopping them.
        yaml = pytest.importorskip("yaml")
        spec = yaml.safe_load(WORKFLOW.read_text(encoding="utf8"))
        assert spec["concurrency"]["cancel-in-progress"] is False

    def test_workflow_does_not_advertise_a_nonexistent_release_flag(self):
        # `make release` has no RELEASE_SHA override; suggesting one implies a
        # pin that does not happen.
        assert "RELEASE_SHA" not in WORKFLOW.read_text(encoding="utf8")

    def test_workflow_uses_standard_provisioning(self):
        # SPOT preemption produces retries that read as flakes; a gate people
        # learn to ignore is not a gate.
        text = WORKFLOW.read_text(encoding="utf8")
        assert "PDD_CLOUD_BATCH_SPOT_PROVISIONING_MODEL: STANDARD" in text

    def test_workflow_allows_the_gate_to_finish_polling(self):
        yaml = pytest.importorskip("yaml")
        spec = yaml.safe_load(WORKFLOW.read_text(encoding="utf8"))
        timeout = spec["jobs"]["cloud-test"]["timeout-minutes"]
        # Worst case is image rebuild (cloudbuild timeout 1800s = 30min) plus
        # submit.sh POLL_TIMEOUT (7200s = 120min) plus checkout/auth ~= 152min.
        # A 150-minute budget severs the runner just before it reports.
        assert timeout > 152

    def test_workflow_caches_the_image_build_marker(self):
        # `.cloud-image-hash` is gitignored, so without a cache every run does a
        # full Cloud Build image rebuild.
        text = WORKFLOW.read_text(encoding="utf8")
        assert "actions/cache" in text
        assert ".cloud-image-hash" in text
