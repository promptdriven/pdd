"""Generation evidence audit module (issue #1466).

Produces a machine-readable GenerationAuditRecord mapping source requirements
to generated files, tests, contracts, and validation gate results.

Extends evidence_manifest patterns (SHA256, .pdd/evidence/ storage, ManifestView).
All processing is deterministic — no LLM calls.
"""
from __future__ import annotations

import json
import logging
import sys
from pathlib import Path
from typing import Optional

from pdd.generation_source_contract import (
    AuditEntryStatus,
    GenerationAuditRecord,
    GenerationSourceContract,
    RequirementAuditEntry,
)

logger = logging.getLogger(__name__)

_DEFAULT_OUTPUT_DIR = Path(".pdd") / "evidence" / "generation-audit"


def build_audit(contract: GenerationSourceContract) -> GenerationAuditRecord:
    """Build a GenerationAuditRecord from a GenerationSourceContract.

    Each FeatureRequirement gets one RequirementAuditEntry. Requirements
    without generated files default to AuditEntryStatus.skipped.
    """
    entries: list[RequirementAuditEntry] = []

    for req in contract.requirements:
        status = AuditEntryStatus.skipped  # default — not yet implemented
        entry = RequirementAuditEntry(
            requirement_id=req.req_id,
            generated_files=[],
            generated_tests=[],
            contracts=[],
            validation_gates={},
            status=status,
        )
        entries.append(entry)

    # Determine overall status
    if not entries:
        overall_status = AuditEntryStatus.skipped
    elif all(e.status == AuditEntryStatus.covered for e in entries):
        overall_status = AuditEntryStatus.covered
    elif any(e.status == AuditEntryStatus.failed for e in entries):
        overall_status = AuditEntryStatus.failed
    elif any(e.status == AuditEntryStatus.partial for e in entries):
        overall_status = AuditEntryStatus.partial
    else:
        overall_status = AuditEntryStatus.skipped

    record = GenerationAuditRecord(
        run_id=contract.run_id,
        source_contract_id=contract.run_id,
        requirements=entries,
        overall_status=overall_status,
        schema_version=1,
    )

    logger.debug(
        "build_audit: run_id=%s, requirements=%d, overall_status=%s",
        record.run_id,
        len(entries),
        overall_status.value,
    )
    return record


def persist_audit(
    record: GenerationAuditRecord,
    output_dir: Optional[Path] = None,
) -> Path:
    """Serialize a GenerationAuditRecord to JSON and write it to disk.

    Returns the path of the written file.
    """
    out_dir = output_dir or _DEFAULT_OUTPUT_DIR
    out_dir.mkdir(parents=True, exist_ok=True)

    filename = f"{record.run_id}.json"
    output_path = out_dir / filename

    data = json.loads(record.model_dump_json())
    output_path.write_text(
        json.dumps(data, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    logger.info("persist_audit: wrote audit to %s", output_path)
    return output_path


def load_audit(
    run_id: str,
    output_dir: Optional[Path] = None,
) -> GenerationAuditRecord:
    """Load a GenerationAuditRecord from disk by run_id.

    Raises FileNotFoundError if the audit file does not exist.
    """
    out_dir = output_dir or _DEFAULT_OUTPUT_DIR
    filename = f"{run_id}.json"
    input_path = out_dir / filename

    if not input_path.exists():
        raise FileNotFoundError(
            f"Audit file not found for run_id={run_id!r}: {input_path}"
        )

    data = json.loads(input_path.read_text(encoding="utf-8"))
    return GenerationAuditRecord.model_validate(data)


def check_audit(
    run_id: str,
    output_dir: Optional[Path] = None,
    *,
    strict: bool = False,
) -> None:
    """Check a persisted audit for completeness.

    When strict=True and any P0 requirements are not covered, calls sys.exit(1).
    When strict=False, logs warnings but does not exit.
    """
    try:
        record = load_audit(run_id, output_dir=output_dir)
    except FileNotFoundError as exc:
        logger.error("check_audit: %s", exc)
        if strict:
            sys.exit(1)
        return

    missing = [
        e for e in record.requirements
        if e.status not in (AuditEntryStatus.covered, AuditEntryStatus.waived)
    ]

    if missing:
        msg = (
            f"Audit {run_id!r}: {len(missing)} requirement(s) are not covered or waived: "
            + ", ".join(e.requirement_id for e in missing[:10])
        )
        if strict:
            logger.error(msg)
            sys.exit(1)
        else:
            logger.warning(msg)
    else:
        logger.info("check_audit: run_id=%s — all requirements covered or waived", run_id)
