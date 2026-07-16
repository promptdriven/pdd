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

## Semantic review evidence

Against the reviewed `origin/main` base, this reconciliation changes 427 prompt
files. Removing only `pdd-reason`, `pdd-interface`, and `pdd-dependency` blocks
leaves 418 prompt bodies byte-for-byte unchanged. Those metadata-only units are
partitioned as follows:

- 190 Python artifacts and 54 TypeScript/React artifacts whose declared public
  surfaces are checked against the current code by the independent audit;
- 165 runtime `*_LLM.prompt` artifacts whose prompt bodies are unchanged and
  whose callable metadata remains an architecture assertion rather than an
  executable code-interface proof; and
- 9 non-Python/TypeScript or externally owned units: Makefile, two CSV files,
  Bash, Fish, Zsh, RST, TOML, and the packaged
  `src/clients/github_client_Python.prompt` owned by `pdd_cloud`.

Within the 418 metadata-only units, 234 gain a missing reason and 274 gain a
missing interface; all final metadata agrees with `architecture.json`. This is
inventory and public-surface evidence, not a claim that every unchanged prompt
requirement has a dedicated behavioral test.

Nine prompts differ after metadata removal. One,
`remote_session_python.prompt`, changes whitespace only. The other eight
back-propagate existing observable code behavior:

- `agentic_common_python.prompt`: shared steering compatibility functions;
- `checkup_planner_python.prompt`: injected LLM planning with deterministic,
  complete fallback;
- `checkup_review_loop_python.prompt`: public parsing, final-state, and final-gate
  compatibility boundaries;
- `fix_verification_errors_loop_python.prompt`: lossless compressed-context
  forwarding for initial and iterative cloud repair calls;
- `frontend/components/ModuleNode_typescriptreact.prompt`: focus-mode dimming;
- `operation_log_python.prompt`: content-free agentic-fallback aggregation;
- `story_regression_gate_python.prompt`: the compatibility evaluator and honest
  non-execution status aliases; and
- `sync_determine_operation_python.prompt`: retained legacy directory constants
  alongside dynamic path resolution.

Each of those eight behaviors exists in the checked-in artifact and has focused
tests. The ModuleNode focus assertion was added to the existing frontend test
suite during this review. The LLM-runtime group remains the explicit evidence
gap: unchanged prompt bodies and synchronized metadata do not prove provider
behavior without executing their owning orchestrator tests or live providers.
The frontend assertion could not be executed in the review worktree because its
`node_modules` dependencies were absent. In addition,
`fix_verification_errors_loop_python.prompt` names the compressed-context
renderer used by its code but does not register that generation dependency;
the exact omitted edge is recorded in
`.pdd/repository-sync-classifications.json` as visible follow-up debt.

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

## Canonical fingerprint migration

Canonical v2 fingerprints bind the prompt, recursive include closure, owned
code, verification artifacts, the nearest governing `.pddrc`, and the exact
authoritative `architecture.json`. Missing or ambiguous governance is a blocker.
Legacy `.pdd/meta/*.json` records are input evidence only; migration never
promotes or rewrites them.

Start with a read-only page. `--module` accepts exact prompt paths and may be
repeated; use `--full-repository` instead for a complete stable scan. The review
manifest is strict schema 1 and is bound to the repository ID, exact head SHA,
reviewer, rationale, and the `after_digest` returned for each unit.

```bash
pdd migrate-fingerprints \
  --base-ref origin/main \
  --head-ref HEAD \
  --full-repository \
  --limit 100 \
  --review-manifest /absolute/path/reviewed-fingerprints.json
```

Dry-run is the default and writes nothing. `NO_OP` preserves an equivalent
canonical record. New or changed records remain semantic `UNKNOWN` and require
trusted validation; the planner never stamps `VERIFIED`. `--apply` delegates a
single reviewed module to the existing transactional trusted-finalization path.
Multi-unit apply is deliberately blocked because an atomic repository-wide
trusted transaction is not available; apply reviewed modules one at a time with
an external replay ledger. Keep using the returned `--cursor` until it is null.

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
