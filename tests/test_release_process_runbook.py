"""Contract tests for the canonical PDD CLI release runbook."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RUNBOOK = ROOT / "docs" / "contributors" / "pdd-cli-release-process.md"
ONBOARDING = ROOT / "docs" / "ONBOARDING.md"


def runbook_text() -> str:
    """Return the canonical release runbook as checked-in text."""
    return RUNBOOK.read_text(encoding="utf8")


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


def test_release_runbook_requires_mutation_disclosure_and_final_evidence():
    text = runbook_text()

    assert "target, rollback path, and risk" in text
    assert "authoritative `final-evidence.json`" in text
    for field in (
        "releaseTag",
        "releaseGitSha",
        "pypiUrl",
        "githubReleaseUrl",
        "cloudTest",
        "pdsProjectId",
        "requestHash",
        "attemptId",
        "agentRunId",
        "stitchedGeneration",
        "stitchedSha256",
        "promotedAuditGeneration",
        "promotedAuditSha256",
        "distributionPackageReceipt",
        "distributionDryRunReceipt",
        "distributionPublishReceipt",
        "youtubeVideoId",
        "youtubeTitle",
        "youtubeChannel",
        "youtubePrivacy",
        "captionReceipt",
        "thumbnailReceipt",
        "discordMarker",
        "discordWorkflowRunUrl",
        "closureIssueUrl",
    ):
        assert f"`{field}`" in text
    assert "historical/intermediate" in text


def test_release_runbook_recovery_is_non_duplicating_and_fail_closed():
    text = runbook_text()

    assert "## Terminal decision tree" in text
    assert "## Warnings versus blockers" in text
    assert "must never create or push another package tag" in text
    assert "must never republish to PyPI" in text
    assert "must never weaken, bypass, or relabel a failed audit" in text
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

    assert "contributors/pdd-cli-release-process.md" in text
    assert "canonical release runbook" in text.lower()
