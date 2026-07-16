"""Semantic contract tests for the canonical PDD CLI release runbook."""

import json
from pathlib import Path
import re
import tomllib


ROOT = Path(__file__).resolve().parents[1]
RUNBOOK = ROOT / "docs" / "contributors" / "pdd-cli-release-process.md"
ONBOARDING = ROOT / "docs" / "ONBOARDING.md"
MAKEFILE = ROOT / "Makefile"
RELEASE_WORKFLOW = ROOT / ".github" / "workflows" / "release.yml"
PYPROJECT = ROOT / "pyproject.toml"


def runbook_text() -> str:
    """Return the canonical release runbook as checked-in text."""
    return RUNBOOK.read_text(encoding="utf8")


def runbook_section(start: str, end: str | None = None) -> str:
    """Extract a runbook section for command and ordering assertions."""
    text = runbook_text()
    start_offset = text.index(start)
    end_offset = text.index(end, start_offset) if end else len(text)
    return text[start_offset:end_offset]


def final_evidence_example() -> dict:
    """Parse the final evidence JSON example as executable documentation."""
    section = runbook_section("## Authoritative final evidence", "## Issue routing")
    match = re.search(r"```json\n(?P<json>.*?)\n```", section, re.DOTALL)
    assert match is not None
    return json.loads(match.group("json"))


def test_release_runbook_is_current_and_covers_the_ordered_lifecycle():
    text = runbook_text()

    assert "@promptdriven/pds@0.1.11" in text
    assert "0.1.7" not in text
    assert "v0.0.305" not in text

    ordered_contracts = [
        "## 1. Derive the candidate",
        "## 2. Cloud test",
        "## 3. PR, review, and merge",
        "## 4. Release from clean `main`",
        "## 5. Approve and verify package publication",
        "## 6. Create, audit, and distribute the release video",
        "## 7. Verify the live YouTube resource",
        "## 8. Complete Discord and release closeout",
    ]
    positions = [text.index(contract) for contract in ordered_contracts]
    assert positions == sorted(positions)


def test_release_runbook_uses_the_distribution_declared_by_pyproject():
    text = runbook_text()
    with PYPROJECT.open("rb") as pyproject_file:
        distribution = tomllib.load(pyproject_file)["project"]["name"]

    assert distribution == "pdd-cli"
    assert 'PYPI_PROJECT="$(python -c' in text
    assert "tomllib.load" in text
    assert 'python -m pip index versions "$PYPI_PROJECT"' in text
    assert 'https://pypi.org/project/${PYPI_PROJECT}/${NEXT_VERSION}/' in text
    assert "PyPI project `pdd`" not in text


def test_normal_release_has_one_video_creation_authority():
    release_section = runbook_section(
        "## 4. Release from clean `main`",
        "## 5. Approve and verify package publication",
    )
    normal_video_section = runbook_section(
        "## 6. Create, audit, and distribute the release video",
        "### Status and safe recovery",
    )
    makefile = MAKEFILE.read_text(encoding="utf8")
    workflow = RELEASE_WORKFLOW.read_text(encoding="utf8")
    compact_video_section = " ".join(normal_video_section.split())

    assert "make --no-print-directory release-video" in makefile
    assert "make release-video" in workflow
    assert 'RELEASE_VIDEO=0 make release-local BUMP="$BUMP"' in release_section
    assert "sole normal creation authority" in compact_video_section
    assert "tag-triggered `.github/workflows/release.yml`" in normal_video_section
    assert not re.search(r"(?m)^make release-video(?:\s|$)", normal_video_section)
    assert "authoritative status proves that no attempt was started" in runbook_text()


def test_runbook_documents_manual_exact_oid_release_lease_recovery():
    release_section = runbook_section(
        "### pdd_cloud attested-release boundary",
        "## 5. Approve and verify package publication",
    )

    assert "There is deliberately **no automatic TTL**" in release_section
    assert "inspect-lease --lease-ref" in release_section
    assert "recover-stale-lease" in release_section
    assert "--force-with-lease" in release_section
    assert "never delete a successor lease" in release_section
    assert "SIGKILL recovery follows this same manual procedure" in release_section


def test_approval_and_post_publish_evidence_match_workflow_ordering():
    workflow = RELEASE_WORKFLOW.read_text(encoding="utf8")
    publish_job = workflow[workflow.index("  publish-pypi:") :]
    approval_section = runbook_section(
        "## 5. Approve and verify package publication",
        "## 6. Create, audit, and distribute the release video",
    )

    compact_approval = " ".join(approval_section.split())

    assert publish_job.index("environment: pypi-publish") < publish_job.index("steps:")
    assert "before checkout, build, Twine verification, and publication" in compact_approval
    assert "attestations do not exist yet" in compact_approval
    assert approval_section.index("Before approval") < approval_section.index(
        "After publication"
    )


def test_same_tag_recovery_is_non_destructive_and_does_not_reinvoke_video():
    recovery = runbook_section(
        "### Same-tag package workflow recovery",
        "## 6. Create, audit, and distribute the release video",
    )

    assert 'gh run rerun "$RUN_ID" --repo promptdriven/pdd' in recovery
    assert "video step did not start" in recovery
    assert "no matching production tag-push run exists" in recovery
    assert "verify PyPI first" in recovery
    assert "make release-local" not in recovery
    assert "gh workflow run" not in recovery
    assert "delete" not in recovery.lower()
    assert "re-push" not in recovery.lower()


def test_remote_tag_is_peeled_and_bound_to_release_sha():
    package_evidence = runbook_section(
        "## 5. Approve and verify package publication",
        "## 6. Create, audit, and distribute the release video",
    )

    assert 'refs/tags/$RELEASE_TAG^{}' in package_evidence
    assert 'REMOTE_TAG_SHA="$PEELED_TAG_SHA"' in package_evidence
    assert 'test "$REMOTE_TAG_SHA" = "$RELEASE_GIT_SHA"' in package_evidence


def test_final_evidence_is_parseable_and_only_represents_terminal_states():
    evidence = final_evidence_example()
    text = runbook_text()

    assert evidence["schemaVersion"] == 1
    assert {
        "releaseTag",
        "releaseGitSha",
        "pypiUrl",
        "cloudTest",
        "agentRunId",
        "stitchedGeneration",
        "promotedAuditGeneration",
        "distributionPublishReceipt",
        "youtubeVideoId",
        "discordMarker",
        "closureIssueUrl",
    } <= evidence.keys()
    assert evidence["terminalState"] == "video-published | video-skipped"
    assert "recovery-active" not in evidence["terminalState"]
    assert isinstance(evidence["missingEvidenceReasons"], dict)
    assert "recovery-checkpoint-<sequence>.json" in text
    assert "previousCheckpointSha256" in text
    assert "active recovery is not final closeout" in text
    assert "pending" not in evidence["discordMarker"]


def test_skip_supersession_requires_exact_reconciliation_before_backfill():
    skip_section = runbook_section(
        "### Explicit no-video skip",
        "## Terminal decision tree",
    )

    compact_skip = " ".join(skip_section.split())

    assert "refuses to backfill while a matching skip record remains" in compact_skip
    assert "remove_release_video_skip_records" in skip_section
    assert "verify the edited release body contains neither the skip text nor marker" in compact_skip
    assert "allowed only before `final-evidence.json` exists" in compact_skip
    assert skip_section.index("remove_release_video_skip_records") < skip_section.index(
        "release-video-discord-backfill"
    )


def test_release_runbook_recovery_is_non_duplicating_and_fail_closed():
    text = runbook_text()

    assert "## Terminal decision tree" in text
    assert "## Warnings versus blockers" in text
    assert "must never create or push another package tag" in text
    assert "must never republish to PyPI" in text
    assert "must never weaken, bypass, or relabel a failed audit" in text
    assert "target, rollback path, and risk" in text
    for marker in (
        "pdd-release-video-discord-backfill-pending",
        "pdd-release-video-discord-backfill",
        "pdd-release-video-skipped",
    ):
        assert marker in text
    for live_check in ("title", "channel", "privacy", "captions", "thumbnail"):
        assert f"**{live_check}**" in text


def test_onboarding_points_maintainers_to_the_canonical_runbook():
    text = ONBOARDING.read_text(encoding="utf8")
    compact = " ".join(text.split())

    assert "contributors/pdd-cli-release-process.md" in text
    assert "canonical release runbook" in text.lower()
    assert "RELEASE_VIDEO=0 make release-local" in text
    assert "Use `RELEASE_VIDEO=0` only for an emergency release" not in text
    assert "leaves the tag-triggered Actions video path enabled" in compact
