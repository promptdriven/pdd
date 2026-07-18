# Agentic Sync V1 scope planning

`pdd sync <issue>` freezes a serializable `pdd.sync.plan.v1` before it gives a
child runner permission to generate files. Module IDs are canonical,
slash-qualified paths. A legacy basename is accepted only where it maps to one
candidate; an ambiguous basename is rejected with its path-qualified choices.

Selection precedence is deterministic:

1. An explicit fallback scope (`PDD_EXPLICIT_SYNC_SCOPE_V1`) is checked against
   the frozen primary candidate set and both Wave 0 digests.
2. `PDD_CHANGED_MODULES` supplies explicit candidates, after canonical alias
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
operation, dependency/SCC order, confidence, and provenance. Its plan digest
is SHA-256 of `pdd.sync.plan.v1\n` plus canonical JSON; its selection digest is
SHA-256 of `pdd.sync.selection.v1\n` plus the canonical sorted module-ID array.
