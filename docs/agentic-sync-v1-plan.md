# Agentic Sync V1 scope planning

`pdd sync <issue>` freezes a serializable `pdd.sync.plan.v1` before it gives a
child runner permission to generate files. Module IDs are canonical,
slash-qualified paths. A legacy basename is accepted only where it maps to one
candidate; an ambiguous basename is rejected with its path-qualified choices.
The runner consumes frozen selected IDs, canonical dependency evidence, and a
separate dependency-safe execution order as its schedule. The latter retains an
authoritative caller order only for independent ready targets or members of the
same SCC. Scheduling operates on the condensed SCC DAG, so a component remains
contiguous and every prerequisite component completes before its dependents.
It writes immutable full-primary `pdd.sync.scope-evidence.v1` plan evidence
under `.pdd/evidence/sync-plans/<plan-digest>.json` and a separate bounded
execution-selection artifact under `.pdd/evidence/sync-executions/`. A fallback
never overwrites the primary plan artifact. These are inputs to a later
result-envelope builder, not `pdd.sync.result.v1` envelopes themselves; Cloud
must copy the ignored local primary-plan artifact to the exact-SHA fallback
checkout.

Selection precedence is deterministic:

1. `PDD_SYNC_SCOPE_SOURCE=fallback_payload_v1` is exclusive. It requires the
   closed `PDD_EXPLICIT_SYNC_SCOPE_V1` object and rejects a present
   `PDD_CHANGED_MODULES`; PDD loads the primary evidence by plan digest and
   never rediscovers fallback scope from a diff or architecture file.
2. `PDD_CHANGED_MODULES` supplies authoritative ordered normal selection, but
   never creates candidates. Every parsed alias must resolve against the
   architecture-backed inventory before dry-run: an unknown entry, runtime-only
   template, ambiguous bare leaf, or unowned path prefix rejects the entire
   selection without an LLM call. A path-qualified alias must be proven by a
   declared filepath, scoped origin, governing context, or frozen candidate;
   requested targets retain caller order only where dependency-safe while
   transitive dependencies remain frozen in canonical graph order.
3. Changed prompt paths from the branch diff supply path-aware candidates.
4. Architecture entries supply prompt/output paths and dependency edges.
5. When architecture is absent, discovery is limited to `prompts/` under the
   governing `.pddrc` root; it records lower-confidence provenance and never
   scans arbitrary repository content.
6. Only unresolved choices may be sent to an ambiguity agent. Its compact
   protocol contains at most 64 candidate IDs, compact metadata, and an
   explicitly untrusted size-bounded issue number/title/body excerpt. It never
   includes comments, repository content, architecture, commands, or unbounded
   issue text. The sole accepted response field is a sorted, unique
   `selected_module_ids` subset; commands, paths, prose, dependency edits, and
   invented IDs fail closed.

The plan records governing root/context, prompt and output paths, reason,
operation, dependency/SCC order, confidence, and provenance. Required
dependencies are retained transitively; a candidate edge outside the frozen set
is an error, not an omitted scheduling hint. Both normal and fallback lists are
limited to 64 IDs. Its plan digest is SHA-256 of `pdd.sync.plan.v1\n` plus
canonical JSON; its selection digest is SHA-256 of `pdd.sync.selection.v1\n`
plus the canonical sorted module-ID array. Fallback children receive only the
validated explicit scope and do not inherit ambient changed-module selection.

Durable execution receives the exact checkout SHA captured by the planner. It
rejects a missing or changed current SHA before preparing a worktree and never
rewrites this authority. Checkpoint trailers use `PDD-Sync-Checkpoint-V2` with
the immutable attempt kind, plan digest, selection digest, ordered graph, and
checkout identity; only an exact binding match may resume a module on a fresh
clone. Each child unit is relocated into its own worktree before it runs. Before
checkpoint staging, durable mode examines tracked and untracked changes and
permits only the selected candidate's frozen `output_paths` plus target-scoped
`.pdd/meta/<target>_*.json`; an out-of-scope mutation fails rather than becoming
an empty successful checkpoint.
