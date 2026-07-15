# PDD Dogfood Reconciliation Runbook

Tracking issue: [promptdriven/pdd#2079](https://github.com/promptdriven/pdd/issues/2079)

This runbook documents the bounded, four-phase manual process for establishing an
audited PDD dogfood baseline using current tooling, within the following safety
invariants:

- No PDD mutation commands (`pdd generate`, `pdd sync`, `pdd update`, `pdd fix`)
  are used during the audit.
- `pdd baseline --accept-current` is used only for modules where existing tests
  pass and the public interface matches the prompt's declared contract.
- All accepted modules receive semantic `UNKNOWN` (not `IN_SYNC`) until trusted
  validation evidence is recorded via the full sync core (PR 13 exit gate).
- Every fingerprint written must be preceded by documented evidence collection.

This process is the pragmatic equivalent of PR 13 in
[`docs/global_sync_resolution_plan.md`](global_sync_resolution_plan.md) while
PRs 1–12 (sync core) are in progress. It does not satisfy PR 13's full exit
gate; it produces a documented, idempotent starting point.

## Three status dimensions

Every module is classified on all three axes before any write:

| Dimension | Values |
| --- | --- |
| Inventory | `MANAGED`, `HUMAN_OWNED`, `REMOVED`, `INVALID` |
| Baseline | `CURRENT`, `DRIFTED`, `UNBASELINED`, `CORRUPT` |
| Semantic | `VERIFIED`, `UNKNOWN`, `CONFLICT`, `FAILED` |

`IN_SYNC` is NOT a valid output of this process. A baseline reset produces
`CURRENT + UNKNOWN`, not `IN_SYNC`.

---

## Phase 1 — Complete Inventory (no writes)

**Goal:** A single audit artifact listing every prompt/code pair with its
three-dimensional status. No fingerprints are written in this phase.

**Steps:**

1. Build a candidate list from four independent sources. Reconcile their union:
   - `git ls-files | grep '\.prompt$'` — raw filesystem inventory
   - Prompt directory scan (`find pdd/prompts -name '*.prompt'`)
   - Parse `architecture.json` entries (top-level pairs)
   - Scan `.pdd/fingerprints/` for existing fingerprint files

2. For each candidate, assign inventory status:
   - `MANAGED` — prompt and code file both present; prompt is the source of truth
   - `HUMAN_OWNED` — code exists without a governing prompt, or explicitly declared
   - `REMOVED` — formerly tracked unit with tombstone record
   - `INVALID` — build-generated (e.g., `_version.py`), ambiguous leaf, or
     duplicate; classify by ownership/source rule, not environment-specific waiver

3. For each MANAGED candidate, check baseline status:
   - `CURRENT` — fingerprint file exists and matches current bytes
   - `DRIFTED` — fingerprint exists but hash differs
   - `UNBASELINED` — no fingerprint file exists
   - `CORRUPT` — fingerprint exists but is malformed

4. For each MANAGED candidate, assign semantic status:
   - `VERIFIED` — existing test suite passes AND public function/class signatures
     match the prompt's `<pdd-interface>` or declared contract
   - `UNKNOWN` — tests pass but no declared interface, or interface not verified
   - `CONFLICT` — code diverges from prompt in an unresolved way
   - `FAILED` — existing tests fail against current code

5. Write the result as a checked-in CSV or JSON audit artifact:
   `docs/audit/reconciliation_inventory_YYYY-MM-DD.csv`
   Columns: `prompt_path`, `code_path`, `inventory`, `baseline`, `semantic`,
   `evidence_notes`

**Known edge cases:**
- Discovery masking: `pdd reconcile` may report `unbaselined=0` when
  metadata-backed discovery is active. Use the four-source union, not
  `pdd reconcile` alone, for the authoritative count.
- Wrong `.pddrc` context: scope all `pdd reconcile` calls with `--module`
  to avoid the unregistered top-level prompt misclassification bug.
- Human-owned tests: classify per-artifact, not by file path convention.
- Build-generated files: exclude via ownership/source rule.

**Exit criterion:** CSV/JSON artifact committed. Row count equals the union
of all four sources. Every row has an inventory, baseline, and semantic value.
No writes to fingerprint files.

---

## Phase 2 — Architecture Repair (structure-only PR)

**Goal:** Every prompt/code pair visible to `pdd reconcile` and
`pdd sync-architecture`. Zero cycles in the dependency graph.

**Steps:**

1. Run `pdd sync-architecture --dry-run` and capture its output and exit code.

2. For each invisible module identified in Phase 1 that is not in
   `architecture.json`, diagnose the root cause individually:
   - (a) Missing `architecture.json` entry → add it with correct paths
   - (b) Correct entry exists but path mapping is wrong → fix the mapping
   - (c) Module registered under a different `.pddrc` context → move or add entry
   - (d) Intentionally human-owned → declare as `HUMAN_OWNED` with rationale;
     do NOT add a managed entry

3. After adding entries, re-run `pdd sync-architecture --dry-run`. If non-zero,
   parse the error output for cycle and missing-dependency errors. Fix cycles
   first (remove or correct the offending edges), then re-run. Repeat until
   exit code is 0.

4. Review the proposed updates individually; apply only those that are
   structural corrections, not data baseline changes.

5. Open a structure-only PR containing only `architecture.json` changes and
   the Phase 1 inventory artifact.

**Exit criterion:** `pdd sync-architecture --dry-run` exits 0 on a clean
checkout. No fingerprint writes. `architecture.json` entry count equals the
expected managed unit count from Phase 1.

---

## Phase 3 — Semantic Audit and Evidence Collection

**Goal:** Per-module evidence notes. Prompts annotated where code has diverged.

**Steps:**

1. For each MANAGED module in the Phase 1 inventory:
   - Run its associated test file(s): `pytest tests/test_<module>.py -v`
   - Check the public function/class signatures against the prompt's
     `<pdd-interface>` declaration or declared contract section
   - Record pass/fail and interface match in the evidence column of the
     audit CSV

2. For modules where code has diverged from the prompt (semantic `CONFLICT`
   or `UNKNOWN`), back-propagate at observable-contract altitude:
   - Add a structured annotation block to the prompt (do NOT re-generate code):
     ```
     % Back-propagated observable contract (YYYY-MM-DD, issue #2079):
     % Actual signature: <function_name>(<args>) -> <ReturnType>
     % Key behaviors observed: <list>
     % Divergence from declared contract: <description>
     % Tracking: <issue or PR>
     ```
   - This is documentation, not a PDD mutation command.

3. Produce per-module evidence notes as a separate checked-in artifact or
   as inline annotations in the audit CSV.

**Exit criterion:** Every MANAGED module has a `semantic` value and
`evidence_notes` entry in the audit CSV. No fingerprint writes. Prompt
annotations are committed for any module with a documented divergence.

---

## Phase 4 — Fingerprint Baseline + CI Read-Only Gate (data-only PR)

**Goal:** Fingerprints for semantically verified modules. A CI gate that
passes twice with no writes.

**Steps:**

1. For each module where Phase 3 produced semantic `VERIFIED` (tests pass
   AND interface matches prompt):
   ```bash
   pdd baseline --accept-current <MODULE> \
     --reason "Audited: tests pass, interface matches prompt. issue #2079"
   ```
   Confirm the command records semantic `UNKNOWN` (not `IN_SYNC`) — this is
   correct; `IN_SYNC` requires the full sync core trust chain.

2. For modules with semantic `UNKNOWN`, `CONFLICT`, or `FAILED`: do NOT
   baseline. Open a tracked issue for each with the divergence details from
   Phase 3.

3. Open a data-only PR (no logic changes, no enforcement activation) containing:
   - The fingerprint files written in step 1
   - The final audit CSV/JSON

4. After the data PR merges, verify idempotency:
   ```bash
   # Run 1
   pdd reconcile --check > /tmp/reconcile_run1.json 2>&1; echo "Exit: $?"
   # Run 2 (no writes between runs)
   pdd reconcile --check > /tmp/reconcile_run2.json 2>&1; echo "Exit: $?"
   # Verify byte-identical output
   diff /tmp/reconcile_run1.json /tmp/reconcile_run2.json
   ```
   Both runs must exit 0 and produce byte-identical output.

5. Do NOT activate merge enforcement (that is PR 14 in the sync resolution
   plan, after PR 13's full exit gate is satisfied).

**Exit criterion:** Two consecutive `pdd reconcile --check` runs exit 0 with
byte-identical output in a clean checkout. Fingerprint count equals the number
of semantically verified modules from Phase 3. Every unverified module has a
tracked issue. No enforcement gate is activated.

---

## Deliverables

| Artifact | Phase | PR |
| --- | --- | --- |
| `docs/audit/reconciliation_inventory_YYYY-MM-DD.csv` | 1 | Structure PR |
| Updated `architecture.json` entries | 2 | Structure PR |
| Prompt back-propagation annotations | 3 | Structure PR |
| Per-module fingerprint files | 4 | Data-only PR |
| Two-run idempotency evidence | 4 | Data-only PR description |

## What this does NOT deliver

- Full `IN_SYNC` status for any unit (requires trusted evidence via sync core)
- Enforcement gate activation (PR 14 equivalent)
- PRD synchronization
- Automatic conflict resolution
- Coverage for semantic `UNKNOWN` units (these require individual follow-up)
