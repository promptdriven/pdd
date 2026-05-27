"""Example: how to use `pdd.metadata_sync.run_metadata_sync`.

This script demonstrates the metadata-sync orchestrator that finalizes
prompt metadata (tags, architecture, run_report, fingerprint) in a fixed
pipeline. It runs entirely in a temporary directory with `dry_run=True` so
that no on-disk state is mutated.

API summary:
    run_metadata_sync(
        prompt_path: Path,           # path to *.prompt file (input)
        code_path: Optional[Path],   # path to generated code (optional input)
        *,
        dry_run: bool = False,       # if True, no file/state writes
        repo_root: Optional[Path],   # auto-inferred from prompt_path when None
        architecture_path: Optional[Path],  # auto-discovered when None
    ) -> MetadataSyncResult

`MetadataSyncResult` is a Pydantic v2 model with:
    - prompt_path: Path
    - code_path: Optional[Path]
    - dry_run: bool
    - stages: Dict[str, StageStatus]  (keys: prompt, tags, architecture,
                                       run_report, fingerprint)
    - ok: bool                   (property)  — True iff no stage failed.
    - failing_stage: Optional[str] (property) — first failing stage, else None.

`StageStatus` fields:
    - status: Literal["ok", "skipped", "failed", "dry_run"]
    - reason: Optional[str]   (populated when skipped/failed)
    - detail: Optional[str]   (counts, file paths touched, etc.)
"""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path

# Make the local `pdd` package importable regardless of CWD.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.metadata_sync import (  # noqa: E402  (path setup above)
    MetadataSyncResult,
    StageStatus,
    run_metadata_sync,
)


PROMPT_CONTENT = """<pdd-reason>Demo prompt for metadata_sync example.</pdd-reason>
<pdd-interface>{"type": "module", "module": {"functions": []}}</pdd-interface>
<pdd-dependency>other_python.prompt</pdd-dependency>

% You are an expert engineer. Demo content.
"""


def _summarize(result: MetadataSyncResult) -> None:
    """Print a compact summary of a MetadataSyncResult."""
    print(f"  ok            = {result.ok}")
    print(f"  failing_stage = {result.failing_stage}")
    print(f"  dry_run       = {result.dry_run}")
    print("  stages:")
    for name in ["prompt", "tags", "architecture", "run_report", "fingerprint"]:
        stage: StageStatus | None = result.stages.get(name)
        if stage is None:
            print(f"    - {name:12s}: <missing>")
            continue
        line = f"    - {name:12s}: status={stage.status}"
        if stage.detail:
            line += f"  detail={stage.detail}"
        if stage.reason:
            line += f"  reason={stage.reason}"
        print(line)


def main() -> None:
    # Build an isolated workspace inside a temp dir. We need a `prompts/`
    # directory so that infer_module_identity() can extract (basename, language).
    with tempfile.TemporaryDirectory(prefix="metadata_sync_example_") as tmp:
        root = Path(tmp)
        (root / ".pddrc").write_text("# marker for repo_root inference\n", encoding="utf-8")
        prompts_dir = root / "prompts"
        prompts_dir.mkdir()

        prompt_path = prompts_dir / "demo_python.prompt"
        prompt_path.write_text(PROMPT_CONTENT, encoding="utf-8")

        # ----- Case 1: happy path, dry_run=True -----
        # No architecture.json exists, so the `architecture` stage is expected
        # to be `skipped` with reason "no architecture.json found".
        # `tags` stage sees existing PDD tags and reports them as preserved.
        # `run_report` and `fingerprint` stages run in dry_run mode.
        print("=== Case 1: happy path, dry_run=True ===")
        result = run_metadata_sync(prompt_path, dry_run=True)
        _summarize(result)

        # ----- Case 2: missing prompt file -----
        # The `prompt` stage MUST fail and short-circuit the rest of the
        # pipeline. All subsequent stages get marked `skipped`.
        print()
        print("=== Case 2: missing prompt file (short-circuit) ===")
        missing = prompts_dir / "does_not_exist_python.prompt"
        result_missing = run_metadata_sync(missing, dry_run=True)
        _summarize(result_missing)
        # Sanity check: failing_stage must be "prompt".
        assert result_missing.failing_stage == "prompt"
        assert result_missing.ok is False

        # ----- Case 3: idempotent re-run -----
        # Calling run_metadata_sync twice in dry_run mode must produce
        # equivalent on-disk state (no writes) and equivalent results.
        print()
        print("=== Case 3: idempotent re-run (dry_run=True) ===")
        result_again = run_metadata_sync(prompt_path, dry_run=True)
        _summarize(result_again)
        # Stage statuses should match between case 1 and case 3.
        for name in ["prompt", "tags", "architecture", "run_report", "fingerprint"]:
            assert result.stages[name].status == result_again.stages[name].status, (
                f"non-idempotent: stage {name} differs between runs"
            )

        # ----- Case 4: result type is a Pydantic v2 model -----
        print()
        print("=== Case 4: MetadataSyncResult is a Pydantic v2 model ===")
        as_dict = result.model_dump()
        print(f"  keys: {sorted(as_dict.keys())}")
        print(f"  stage names: {sorted(as_dict['stages'].keys())}")

    print()
    print("Example completed successfully.")


if __name__ == "__main__":
    main()
