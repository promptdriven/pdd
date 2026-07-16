# Manual repository synchronization

Use this procedure to reconcile the PDD repository while project-wide `pdd sync`
cannot yet enforce the complete repository invariant. It is a maintainer workflow,
not a replacement implementation for the global sync design in
[`global_sync_resolution_plan.md`](global_sync_resolution_plan.md).

## What “synchronized” means

Repository sync has three separate claims:

1. **Inventory alignment:** every managed prompt, artifact, architecture entry,
   ownership record, and exceptional mapping is present exactly once.
2. **Contract alignment:** prompt-owned purpose, dependencies, and public
   interface agree with `architecture.json` and the checked-in code surface.
3. **Behavioral verification:** current tests and trusted evidence demonstrate
   the prompt requirements against the current artifact bytes.

A clean structural audit proves the first two claims. It does not turn arbitrary
prose and code into a semantic proof. A legacy fingerprint must not be refreshed
merely to hide drift; validation must run first, and evidence must remain
`UNKNOWN` when no trusted validator covers the requirement.

Candidate profile consistency is not protected-base authorization. The
transition loader reads authority from the protected base, so rows introduced
by the same candidate that consumes them cannot authorize themselves. The
transition rows prepared by this reconciliation are exact dormant data, not a
claim that the combined candidate is merge-safe.

## Current repository inventory

The reviewed inventory contains:

- 466 expected managed prompt units;
- 461 `architecture.json` entries;
- 284 conventional prompt-to-artifact pairs;
- 5 reviewed prompt-only units;
- 3 tracked human-owned prompt fixtures;
- 466 candidate profiles internally bound to the current prompt requirements;
- 427 exact opaque requirement-identity transitions from `origin/main`; and
- 44 tracked legacy fingerprints, all currently stale or semantically unknown,
  plus 23 historical run reports.

Exceptional mappings and their rationale live in
`.pdd/repository-sync-classifications.json`. Additions require an explicit,
reviewable classification; absence is never treated as an implicit exception.

## Authoring procedure

1. Create a dedicated worktree, fetch `origin`, and rebase onto `origin/main`.
   Record the exact base SHA before editing.
2. Read [`prompting_guide.md`](prompting_guide.md). Treat each prompt as the
   behavior contract: state purpose and externally observable requirements,
   preserve the existing public interface, add negative rules for important
   failure modes, and avoid prescribing private implementation steps.
3. Run the read-only audit before editing and retain its findings:

   ```bash
   python scripts/repository_sync_audit.py --json
   ```

4. Review missing metadata and interfaces against both the prompt body and the
   current artifact. Use `scripts/manual_repository_sync.py` only for mechanical,
   reviewed transformations. Its write modes are explicit; it does not run PDD's
   sync runtime. LLM-interface normalization doubles literal JSON braces so the
   metadata remains parseable without breaking direct `str.format()` calls.
5. Resolve every finding until the read-only audit reports zero. The audit checks
   inventory, paths, classifications, dependencies, architecture metadata,
   verification profiles, Python public signatures, FastAPI endpoints,
   TypeScript exports, and React props. It reports legacy fingerprint freshness
   separately; zero structural findings does not mean historical evidence is current.
6. Run focused tests for every behavioral conflict, then the complete Python and
   frontend suites. A passing unrelated suite is not evidence for an uncovered
   requirement.
7. Re-run the audit, inspect the complete diff, fetch and rebase again, resolve
   any new conflicts by the rules below, and repeat all affected checks.

The mechanical authoring command used for this repository-wide pass is:

```bash
python scripts/manual_repository_sync.py \
  --complete-registered-prompt-metadata \
  --normalize-llm-interface-metadata \
  --normalize-prompt-reasons \
  --refresh-declared-python-interfaces \
  --write-architecture \
  --write-verification-profiles \
  --write-requirement-rotations
```

Do not run a write mode without reviewing its diff. The independent audit, not
the authoring helper, is the acceptance check.

## Protected landing sequence

This reconciliation cannot safely land as one ordinary pull request under the
current protected transition loader. Use a reviewed two-phase sequence:

1. Establish authority for candidate-added dormant rows through either a
   separately reviewed loader change that permits only strictly dormant rows or
   an administrator-installed protected trust-root update.
2. Land Phase A with the exact 427 future transition rows while prompt and
   verification-profile bytes remain unchanged.
3. Rebase this reconciliation onto that protected Phase A base. Phase B applies
   the reviewed prompt, architecture, and profile bytes, consuming protected
   rows instead of self-authorizing them.

If any prompt or profile byte changes after Phase A is prepared, regenerate and
re-review the exact rows. Never amend digest constants merely to make a failing
transition check pass.

## Conflict rules

| Conflict | Resolution |
| --- | --- |
| Prompt changed, derived artifact unchanged | Preserve prompt intent, update code and tests, then sync architecture metadata. |
| Code changed intentionally, prompt unchanged | Back-propagate the observable behavior into the prompt before updating architecture metadata. |
| Prompt and code both changed | Compare both with their merge base. Combine compatible intent; if requirements contradict, preserve both sides and block for a maintainer decision. |
| Declared interface differs from code | Freeze the established public surface unless an explicit requirement and tests authorize a breaking change. Never expose private helpers just because they are callable. |
| Tests differ from prompt or code | Preserve valid coverage, update assertions to the resolved contract, and add a characterization test before changing ambiguous behavior. |
| Architecture differs from the prompt header | Purpose, dependencies, and interface come from reviewed prompt metadata; the artifact path comes from the existing checked-in artifact or an explicit exceptional mapping. |
| Fingerprint differs from current bytes | Treat it as stale evidence. Validate the resolved unit and finalize evidence/fingerprint state transactionally; never stamp first and infer correctness afterward. |
| Rebase introduces a new conflict | Re-run inventory and interface derivation on the rebased tree. Do not accept either side wholesale or resolve generated JSON by line position. |

When intent cannot be established from the prompt, code, tests, history, or issue,
the correct result is a visible unresolved conflict—not a guessed synchronization.
