"""Read-only advisory layer for ``pdd checkup`` subcommands (``--review explain``)."""
from __future__ import annotations

import json
import logging
import re
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Optional

logger = logging.getLogger(__name__)


@dataclass
class CheckupFinding:
    """One advisory finding from the LLM pass."""

    severity: str
    area: str
    message: str
    evidence: str = ""


@dataclass
class CheckupReport:
    """Advisory pass outcome; does not affect deterministic exit code."""

    status: str
    findings: list[CheckupFinding] = field(default_factory=list)


SKIPPED_REPORT = CheckupReport(status="skipped", findings=[])


def failed_report(message: str) -> CheckupReport:
    """Build a failed advisory report with a single error finding."""
    return CheckupReport(
        status="failed",
        findings=[
            CheckupFinding(
                severity="error",
                area="advisory",
                message=message,
                evidence="",
            )
        ],
    )


def final_exit_code(deterministic: int, report: CheckupReport) -> int:  # pylint: disable=unused-argument
    """Return deterministic exit code unchanged (advisory is non-fatal)."""
    return deterministic


def report_as_dict(report: CheckupReport) -> dict[str, Any]:
    """Serialize a report for JSON embedding."""
    return {
        "status": report.status,
        "findings": [asdict(finding) for finding in report.findings],
    }


def run_advisory_explain(  # pylint: disable=too-many-arguments
    payload: Any,
    *,
    command: str,
    strength: float = 0.5,
    temperature: float = 0.0,
    time: Optional[float] = None,
    verbose: bool = False,
    use_cloud: Optional[bool] = None,
) -> CheckupReport:
    """
    Run a bounded read-only LLM advisory pass over deterministic output.

    Never raises; returns ``failed_report`` on errors.
    """
    try:
        from .llm_invoke import llm_invoke  # pylint: disable=import-outside-toplevel

        template_path = (
            Path(__file__).parent / "prompts" / "checkup_advisory_explain_LLM.prompt"
        )
        if not template_path.is_file():
            logger.warning("checkup_advisory_explain_LLM.prompt not found")
            return failed_report("Advisory template missing")

        template = template_path.read_text(encoding="utf-8")
        filled = (
            template.replace("{command}", command)
            .replace("{payload_json}", json.dumps(payload, indent=2, default=str))
        )
        result = llm_invoke(
            messages=[{"role": "user", "content": filled}],
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            use_cloud=use_cloud,
        )
        response_text = str(result.get("result", ""))
        json_match = re.search(
            r"```(?:json)?\s*(\{.*?\})\s*```", response_text, re.DOTALL
        )
        raw_json = json_match.group(1) if json_match else response_text.strip()
        parsed = json.loads(raw_json)
        findings_raw = parsed.get("findings", []) if isinstance(parsed, dict) else []
        findings: list[CheckupFinding] = []
        for item in findings_raw:
            if not isinstance(item, dict):
                continue
            findings.append(
                CheckupFinding(
                    severity=str(item.get("severity", "warn")),
                    area=str(item.get("area", command)),
                    message=str(item.get("message", "")),
                    evidence=str(item.get("evidence", "")),
                )
            )
        status = str(parsed.get("status", "ok")) if isinstance(parsed, dict) else "ok"
        if findings and status == "ok":
            status = "warned"
        return CheckupReport(status=status, findings=findings)
    except Exception as exc:  # noqa: BLE001  # pylint: disable=broad-exception-caught
        logger.warning("checkup advisory explain failed: %s", exc)
        return failed_report(str(exc))


def advisory_for_review(  # pylint: disable=too-many-arguments
    review: str,
    payload: Any,
    *,
    command: str,
    ctx_obj: Optional[dict[str, Any]] = None,
) -> CheckupReport:
    """Run advisory when ``review == 'explain'``; otherwise return ``SKIPPED_REPORT``."""
    if review != "explain":
        return SKIPPED_REPORT
    obj = ctx_obj or {}
    use_cloud = not bool(obj.get("local", False))
    return run_advisory_explain(
        payload,
        command=command,
        strength=float(obj.get("strength", 0.5)),
        temperature=float(obj.get("temperature", 0.0)),
        time=obj.get("time"),
        verbose=bool(obj.get("verbose", False)),
        use_cloud=use_cloud,
    )
