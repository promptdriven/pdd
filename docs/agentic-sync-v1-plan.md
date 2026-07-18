# Agentic Sync V1 scope planning

`pdd sync <issue>` freezes a serializable `pdd.sync.plan.v1` before it gives a
child runner permission to generate files. Module IDs are canonical,
slash-qualified paths. A legacy basename is accepted only where it maps to one
candidate; an ambiguous basename is rejected with its path-qualified choices.
The runner consumes the frozen selected IDs and dependency order as its schedule
and writes a narrow `pdd.sync.scope-evidence.v1` artifact under
`.pdd/evidence/sync-plans/`. This is plan evidence for a later result-envelope
builder; it is not itself a `pdd.sync.result.v1` result envelope.

Selection precedence is deterministic:

1. `PDD_SYNC_SCOPE_SOURCE=fallback_payload_v1` is exclusive. It requires the
   closed `PDD_EXPLICIT_SYNC_SCOPE_V1` object and rejects a present
   `PDD_CHANGED_MODULES`; PDD loads the primary evidence by plan digest and
   never rediscovers fallback scope from a diff or architecture file.
2. `PDD_CHANGED_MODULES` supplies authoritative normal candidates, after alias
   resolution.
3. Changed prompt paths from the branch diff supply path-aware candidates.
4. Architecture entries supply prompt/output paths and dependency edges.
5. When architecture is absent, discovery is limited to `prompts/` under the
   governing `.pddrc` root; it records lower-confidence provenance and never
   scans arbitrary repository content.
6. Only unresolved choices may be sent to an ambiguity agent. Its compact
   protocol contains bounded candidate IDs and metadata, and a response can
   select only those IDs.

The plan records governing root/context, prompt and output paths, reason,
operation, dependency/SCC order, confidence, and provenance. Required
dependencies are retained transitively; a candidate edge outside the frozen set
is an error, not an omitted scheduling hint. Both normal and fallback lists are
limited to 64 IDs. Its plan digest is SHA-256 of `pdd.sync.plan.v1\n` plus
canonical JSON; its selection digest is SHA-256 of `pdd.sync.selection.v1\n`
plus the canonical sorted module-ID array. Fallback children receive only the
validated explicit scope and do not inherit ambient changed-module selection.
