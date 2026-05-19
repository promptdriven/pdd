# Shared Drift Classifier (design)

Status: design / first implementation.
Tracking: promptdriven/pdd#884 (relates to #860, promptdriven/pdd#727, #1369, #1370).

## Why

PDD classifies artifact drift in several places today:

- `sync_determine_operation()` fingerprint state machine
- `pdd update --all` code-hash / include-dep / git detection
- CI auto-heal detection plus git-diff reclassification
- `pdd change` preflight drift healing
- no-arg `pdd sync` Tier 1 global scan

These paths can legitimately run different repair operations, but the
*stale / artifact-drift classification itself* should be shared so the answer
to "is this repo in sync?" is not command-dependent.

## Scope

This module unifies **classification only**. Repair-plan selection
(`generate` vs `update` vs `auto-deps` vs `ci heal`) remains
command-specific in this PR. Repair unification is tracked separately.

## Public API (sketch)

```python
# pdd/drift_classifier.py

from enum import Enum
from typing import Any, Literal, Mapping, Optional, Sequence
from pydantic import BaseModel

class DriftReason(str, Enum):
    IN_SYNC                = "in_sync"
    PROMPT_CHANGED         = "prompt_changed"
    CODE_CHANGED           = "code_changed"
    EXAMPLE_CHANGED        = "example_changed"
    TEST_CHANGED           = "test_changed"
    INCLUDE_DEP_CHANGED    = "include_dep_changed"
    SOURCE_DOC_CHANGED     = "source_doc_changed"
    ARCHITECTURE_CHANGED   = "architecture_changed"
    MISSING_ARTIFACT       = "missing_artifact"
    FINGERPRINT_MISSING    = "fingerprint_missing"
    GIT_CHANGE_OVERRIDE    = "git_change_override"
    UNKNOWN                = "unknown"

class ArtifactHashes(BaseModel):
    prompt: Optional[str] = None
    code: Optional[str] = None
    example: Optional[str] = None
    tests: Mapping[str, str] = {}
    include_deps: Mapping[str, str] = {}
    source_docs: Mapping[str, str] = {}

class GitChangeSet(BaseModel):
    changed_paths: Sequence[str] = ()
    base_ref: Optional[str] = None
    head_ref: Optional[str] = None

class DriftInputs(BaseModel):
    target: str                                                  # module basename or prompt path
    scope: Literal["sync", "update", "change", "ci", "scan"]     # caller identity; telemetry-only, never branches the verdict
    stored_fingerprint: Optional[Mapping[str, Any]] = None
    stored_run_report: Optional[Mapping[str, Any]] = None
    current_hashes: ArtifactHashes
    architecture_metadata: Optional[Mapping[str, Any]] = None
    prd_metadata: Optional[Mapping[str, Any]] = None
    git_change_set: Optional[GitChangeSet] = None

class DriftVerdict(BaseModel):
    is_drift: bool
    reasons: Sequence[DriftReason]                # canonical-ordered (sorted by enum value)
    stale_artifacts: Sequence[str]                # canonical-ordered subset of {"prompt","code","example","tests","include_deps","source_docs","architecture"}
    confidence: Literal["high", "medium", "low"]
    details: Mapping[str, Any] = {}               # diagnostic, not behavior-bearing

def classify_drift(inputs: DriftInputs) -> DriftVerdict: ...
```

The function is **pure**: no filesystem, network, or git calls. Adapters
at each call site collect hashes / fingerprints / diffs and pass them in.

### Canonical ordering contract

Both `reasons` and `stale_artifacts` are returned in a stable canonical
order so test diffs and telemetry are reproducible across Python dict
iteration:

- `reasons` is sorted by `DriftReason` enum value.
- `stale_artifacts` is sorted lexicographically over its closed vocabulary
  (`"architecture"`, `"code"`, `"example"`, `"include_deps"`, `"prompt"`,
  `"source_docs"`, `"tests"`).

Callers MUST NOT rely on any other ordering.

### Confidence semantics

`confidence` is a closed three-value categorical (`"high" | "medium" | "low"`),
not a numeric score:

- **`high`** — full `stored_fingerprint` present, current hashes computed for
  every artifact the fingerprint claims, and no `UNKNOWN` reason emitted.
- **`medium`** — partial inputs (e.g. fingerprint present but optional
  metadata missing, or only `git_change_set` drives the verdict, or
  `mtime_skew` downgraded a `high` verdict).
- **`low`** — `stored_fingerprint is None` and no `git_change_set` to
  anchor the decision, or any `UNKNOWN` reason emitted.

This keeps callers from synthesizing thresholds on a float and forces them
to handle the three cases explicitly.

### Architecture and PRD metadata

`DriftInputs.architecture_metadata` and `DriftInputs.prd_metadata` are
both optional, both opaque `Mapping[str, Any]`, and both feed the
`ARCHITECTURE_CHANGED` reason / `"architecture"` stale-artifact slot.
Either may be `None` for callers that do not track that signal. When
both are present, either differing from its stored snapshot is sufficient
to mark `"architecture"` stale; the classifier does not distinguish
architecture-only drift from PRD-only drift in the verdict (callers can
inspect `details` if they need that split).

## CI git-diff as explicit input

Today CI auto-heal applies a post-hoc git-diff reclassification step.
Under the shared classifier, the git change set is just a field on
`DriftInputs` (`git_change_set`). Any caller (not only CI) may supply it,
and the classifier treats a path appearing in the diff as a first-class
reason to mark its owning artifact stale.

## Call sites

| Path | Today | After this PR |
|------|-------|---------------|
| `sync_determine_operation()` | inline fingerprint state machine | builds `DriftInputs`, calls `classify_drift`, then maps verdict → operation |
| `pdd update --all` | inline code-hash + include-dep + git checks | builds `DriftInputs` (with `git_change_set`), calls `classify_drift` |
| CI auto-heal detection | inline + git-diff correction | passes `git_change_set` into `classify_drift` |
| `pdd change` preflight | inline drift healing trigger | calls `classify_drift` to decide whether to heal |
| no-arg `pdd sync` Tier 1 scan | inline per-module loop | calls `classify_drift` per module |

Each call site keeps its own *repair* logic. Only the classification
step moves behind `classify_drift`.

## Behavior preservation

The first PR ships characterization tests that pin current outputs for:

- `sync_determine_operation` (full state-machine matrix)
- CI auto-heal detection + git-diff correction
- `pdd change` preflight drift detection

These tests pass against both the old inline logic and the new
`classify_drift`, so the refactor is observationally identical.

## Non-goals (first PR)

- Unifying repair plans across commands.
- Changing exit codes or CLI output.
- Replacing `failure_classification` (runtime test/build failures are a
  different axis from artifact drift).
