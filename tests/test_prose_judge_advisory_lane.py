"""Contract tests for the advisory prose-judge lane.

`prose_judge` tests assert on free-form LLM prose with regex oracles, so a
model rephrasing flips them with no product regression behind it. Four
release-blocking PRs (#2278, #2281, #2283, #2286) were spent widening those
patterns during a release. They must therefore run and report, but never gate.

These tests pin both halves of that contract: the marker is registered and
applied, and the Cloud Batch shard deselects it from the blocking run while
still executing and reporting it.
"""

from __future__ import annotations

import configparser
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
PYTEST_INI = ROOT / "pytest.ini"
ENTRYPOINT = ROOT / "ci" / "cloud-batch" / "entrypoint.sh"
JUDGE_TESTS = ROOT / "tests" / "test_change_call_site_and_retry.py"


def entrypoint_text() -> str:
    """Return the Cloud Batch task entrypoint as checked-in text."""
    return ENTRYPOINT.read_text(encoding="utf8")


class TestMarkerRegistration:
    def test_marker_is_registered_in_the_effective_config(self):
        # pytest.ini wins over pyproject.toml here (pytest reports "ignoring
        # pytest config in pyproject.toml"), so registration must live there or
        # --strict-markers fails the Cloud Batch preflight.
        parser = configparser.ConfigParser()
        parser.read(PYTEST_INI)
        assert "prose_judge:" in parser["pytest"]["markers"]

    def test_marker_survives_strict_marker_collection(self):
        result = subprocess.run(
            [
                sys.executable,
                "-m",
                "pytest",
                "--collect-only",
                "--quiet",
                "--strict-markers",
                "--strict-config",
                "-m",
                "prose_judge",
                "tests/test_change_call_site_and_retry.py",
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        # 0 = collected something, 5 = collected nothing. Anything else means
        # the marker or the config is broken.
        assert result.returncode in (0, 5), result.stdout + result.stderr
        assert "PytestUnknownMarkWarning" not in result.stdout


class TestRealLlmTestsAreAdvisory:
    def test_both_real_prose_judged_classes_carry_the_marker(self):
        text = JUDGE_TESTS.read_text(encoding="utf8")
        for klass in ("class TestCallSiteEnumeration:", "class TestRetrySafety:"):
            index = text.index(klass)
            decorators = text[max(0, index - 200) : index]
            assert "@pytest.mark.prose_judge" in decorators, klass

    def test_deterministic_judge_tests_stay_blocking(self):
        # The judges themselves are tested against fixed strings. Those are
        # deterministic and cheap, so they must keep gating.
        text = JUDGE_TESTS.read_text(encoding="utf8")
        index = text.index("class TestDeterministicChangeJudges:")
        decorators = text[max(0, index - 200) : index]
        assert "@pytest.mark.prose_judge" not in decorators

    def test_blocking_selection_excludes_only_the_two_real_tests(self):
        def collected(marker_args: list[str]) -> int:
            result = subprocess.run(
                [sys.executable, "-m", "pytest", "--collect-only", "-q", *marker_args,
                 "tests/test_change_call_site_and_retry.py"],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            assert result.returncode in (0, 5), result.stdout + result.stderr
            return sum(
                1
                for line in result.stdout.splitlines()
                if line.startswith("tests/") and "::" in line
            )

        assert collected(["-m", "prose_judge"]) == 2
        assert collected(["-m", "not prose_judge"]) == collected([]) - 2


class TestAdvisoryArtifactsRespectTheResultAllowlist:
    """The advisory lane must not break the Cloud Batch artifact contract.

    `verify-result-identities.py` allowlists the results prefix exactly:
    `glob("task_*.log")` must equal `{task_<i>.log}`. An advisory file named
    `task_5_prose_judge.log` therefore made every run abort with a
    credential-boundary error even when all 77 tasks passed. Grep-style tests
    cannot see that, so exercise the real validator.
    """

    def test_advisory_filenames_are_outside_the_task_namespace(self):
        text = entrypoint_text()
        assert "advisory_${TASK_INDEX}_prose_judge.log" in text
        assert "task_${TASK_INDEX}_prose_judge" not in text

    def test_real_validator_accepts_a_results_dir_with_advisory_artifacts(self, tmp_path):
        validator = ROOT / "ci" / "cloud-batch" / "verify-result-identities.py"
        spec = importlib.util.spec_from_file_location("vri", validator)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        project, location, job = "proj", "us-central1", "pdd-test-run-x"
        evidence_path = tmp_path / "evidence.json"
        evidence_path.write_text(
            json.dumps(
                {
                    "candidate_sha": "a" * 40,
                    "candidate_tree": "b" * 40,
                    "source_sha256": "c" * 64,
                    "source_generation": "1",
                    "image_digest": "sha256:" + "d" * 64,
                    "project": project,
                    "location": location,
                    "job_uids": {job: {"uid": "uid-1", "task_indexes": [0]}},
                }
            ),
            encoding="utf8",
        )
        results = tmp_path / "results"
        results.mkdir()
        (results / "task_0.json").write_text(
            json.dumps(
                {
                    "task_index": 0,
                    "identity": {
                        "candidate_sha": "a" * 40,
                        "candidate_tree": "b" * 40,
                        "source_sha256": "c" * 64,
                        "source_generation": "1",
                        "image_digest": "sha256:" + "d" * 64,
                        "job_name": job,
                        "task_group": "group0",
                        "raw_task_index": 0,
                        "task_resource": (
                            f"projects/{project}/locations/{location}/jobs/{job}/"
                            "taskGroups/group0/tasks/0"
                        ),
                    },
                }
            ),
            encoding="utf8",
        )
        (results / "task_0.log").write_text("ok", encoding="utf8")

        # Baseline: the real validator is satisfied.
        module.validate_result_directory(evidence_path, results)

        # The advisory artifacts this change adds must not perturb it.
        (results / "advisory_0_prose_judge.log").write_text("advisory", encoding="utf8")
        (results / "advisory_0_prose_judge_junit.xml").write_text("<x/>", encoding="utf8")
        module.validate_result_directory(evidence_path, results)

        # Guard the regression itself: a task_*-prefixed advisory log breaks it.
        # This is what the original implementation did, on every run.
        (results / "task_0_prose_judge.log").write_text("bad", encoding="utf8")
        with pytest.raises(module.ResultIdentityError):
            module.validate_result_directory(evidence_path, results)

    def test_advisory_verdict_reaches_the_collected_result_json(self):
        # The log files are intentionally not downloaded, so the verdict has to
        # travel in task_N.json — which is collected — or it is invisible.
        text = entrypoint_text()
        assert '"advisory_prose_judge": "${ADVISORY_VERDICT:-not-run}"' in text

    def test_collector_surfaces_the_advisory_verdict(self):
        collector = (ROOT / "ci" / "cloud-batch" / "collect-results.sh").read_text(
            encoding="utf8"
        )
        assert "advisory_prose_judge" in collector
        assert "ADVISORY_NOTES" in collector
        assert "Advisory (did not affect pass/fail)" in collector


class TestCloudShardWiring:
    def test_blocking_run_deselects_prose_judge(self):
        text = entrypoint_text()
        assert 'PYTEST_MARKER_ARGS=(-m "not prose_judge")' in text

    def test_advisory_run_still_executes_them(self):
        text = entrypoint_text()
        assert '-m "prose_judge"' in text
        assert "ADVISORY PASS" in text
        assert "ADVISORY FAIL" in text

    def test_advisory_failure_does_not_fail_the_task(self):
        # The advisory pytest call must capture its exit code rather than
        # propagating it, and must not route through run_test (which exits).
        text = entrypoint_text()
        assert "|| ADVISORY_EXIT=$?" in text
        advisory_block = text[text.index("Advisory prose-judge lane") : text.index('run_test "pytest"')]
        assert "run_test" not in advisory_block

    def test_advisory_log_does_not_clobber_the_task_log(self):
        # run_test writes ${RESULT_LOG}; the advisory lane must use its own
        # file or the blocking failure output is destroyed.
        text = entrypoint_text()
        assert "_prose_judge.log" in text
        assert 'ADVISORY_LOG="${RESULT_LOG}"' not in text

    def test_exit_code_triage_distinguishes_drift_from_harness_faults(self):
        # 31 of 32 chunks hold no prose_judge test (exit 5). Only exit 1 is an
        # actual test failure, so only exit 1 may claim the model rephrased its
        # output; 2/3/4/124 are interrupted/internal/usage/timeout and must not
        # be mislabelled as drift.
        text = entrypoint_text()
        advisory = text[text.index("Advisory prose-judge lane") : text.index('run_test "pytest"')]
        assert 'ADVISORY_VERDICT="absent"' in advisory
        assert 'ADVISORY_VERDICT="pass"' in advisory
        assert 'ADVISORY_VERDICT="fail"' in advisory
        assert 'ADVISORY_VERDICT="lane-error-${ADVISORY_EXIT}"' in advisory
        # The rephrasing explanation must sit under the exit-1 arm only.
        drift_arm = advisory[advisory.index('ADVISORY_VERDICT="fail"') : advisory.index('ADVISORY_VERDICT="lane-error')]
        assert "rephrased" in drift_arm
        lane_error_arm = advisory[advisory.index('ADVISORY_VERDICT="lane-error') :]
        assert "rephrased" not in lane_error_arm
        assert "harness fault" in lane_error_arm

    def test_lane_can_be_made_blocking_again(self):
        text = entrypoint_text()
        assert "PDD_BATCH_PROSE_JUDGE_BLOCKING" in text
