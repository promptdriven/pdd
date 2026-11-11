# Runtime workspace boundary

Own the new `src/runtime/runtime-workspace.mjs`. Load the repository's opt-in authored-file ceiling. Readers, capture and write-target callers use this one authority. Keep the Git root, authored paths and Story selection unchanged. An absent policy preserves existing behavior. This interface is a draft feature choice.

Module function `loadRuntimeWorkspace({root}, files)` returns an immutable `{configured,allowed_paths}` policy. `root` is the canonical Git-root string; the supplied synchronous file port is rooted there. Additive includes remain owned by preflight's existing `pdd-source.json` reader. Native callers can use the default safe filesystem adapter; interpreter callers bind the same actual `files.stat({path})` and `files.read({path})` callback boundaries as a generic port. This transport preserves native method arguments/replies; it does not simulate host filesystem effects. The default adapter checks safe no-link ancestors and regular type before opening. No network, authentication, source mutation or model metadata belongs here.

## Policy configuration

The sole bootstrap path is root `pdd-workspace.json`, a local control file, never automatic uploaded or agent context. Stat it once; absent returns `{configured:false,allowed_paths:[]}` without read. A present file must be a Git-visible UTF-8 regular file with no symlink at its path or ancestors; reject unsafe stat/adapter failures as `workspace-config-unsafe`. Stat size uses preflight's existing source-byte maximum, 10,485,760 bytes; refuse oversize before read. A successful read returns `{content}`. Malformed JSON, wrong shape or invalid entries give `workspace-config-invalid`. Both errors name the control path and safe remedy without its contents.

Accept exactly `{"allowed_paths":["simulation/","contracts/shared.md"]}`. `allowed_paths` is required and is an array of strings. An empty array permits no authored files. No additional keys or CLI override. Reject absolute, home, environment, scheme or drive paths, backslashes, control characters, globs, empty strings/components, dot/traversal components and `.git` components. A single final slash is the directory marker; no other empty component is valid. Retain first occurrence of identical entries in authored order.

A marked directory permits its descendants by complete path components. An unmarked entry permits only that exact file. Thus `simulation/` admits `simulation/tests/order.json`, excludes `simulation-private/order.json`, and does not itself select any Story. `contracts/shared.md` admits that file only. This capability does not infer file kinds from extensions or grant access to a similarly prefixed path.

Dedicated bootstrap policy keeps the existing linked include-only `pdd-source.json` contract intact. Local reads of that source-selection control and the strict binding inventory stay explicit control reads, never permission to read excluded declared source. No generated/replaced config can widen the bootstrap ceiling.

## Access outcomes

Module function `allowsRuntimePath(policy,path)` is the pure permission predicate used by production discovery and read callers. Its path is already normalized by the source owner; false means an optional candidate is skipped before opening. Module function `requireRuntimePath(policy,{path,from,chain,role})` returns that same normalized path, or throws `workspace-path-outside` with requested target, referring chain, policy location and a remedy to correct/move the reference or deliberately change the policy. No file contents enter a diagnostic. These are planned shared native exports, not a second resolver. Preserve original Markdown-relative and repository-root reference meanings.

Every required authored read/stat, upload path, raw reference/preparation input, prepared output and save/hash-write destination must be allowed. Required refusal wins before authentication, capacity/model queries, bridge connection, listener setup or dispatch. Optional excluded names are not opened and do not refuse independent selected work. Name-only Git listing and safe non-following ancestor metadata may establish containment; they cannot load ancestor content.

Ordinary source-link callers require the authored name, every substituted resolution path and the final target to fit the ceiling. Leaving and later returning is a refusal before contents contribute. Existing secret, visibility, regular-file, size, identity/snapshot rules remain additional requirements under their current owner. Stricter no-link write/executable/read callers keep that restriction. The ceiling grants no filesystem/process sandbox or protection against an independently launched program.

Revalidate policy with each capture attempt and before every guide/context refresh or source-sensitive continuation. A policy change discards the old context capability; never combine old permission with new bytes. Private runtime state, credentials and PDD-owned launch artifacts remain local infrastructure, not authored source or extra upload permission.

## Dependencies

None. Native file adapters supply the stated safe stat/read contract. Source resolution and capture safeguards remain with their callers; this module owns only opt-in policy and permission outcomes.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"4a6f49ea49071b05711d95496e0e2408360a20dc1bc103b3a26ae67262e0805c","entries":[{"operation":"loadRuntimeWorkspace","input_schema":{"type":"object","properties":{"root":{"type":"string"}},"required":["root"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"configured":{"type":"boolean"},"allowed_paths":{"type":"array","items":{"type":"string"}}},"required":["configured","allowed_paths"],"additionalProperties":false},"errors":["workspace-config-invalid","workspace-config-unsafe"]}],"calls":[],"resources":[{"name":"files","kind":"port","access":"read","operations":[{"name":"stat","access":"read","arguments_schema":{"type":"object","properties":{"path":{"type":"string"}},"required":["path"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"exists":{"type":"boolean"},"is_symlink":{"type":"boolean"},"size":{"type":"integer","minimum":0}},"required":["exists","is_symlink","size"],"additionalProperties":false}},{"name":"read","access":"read","arguments_schema":{"type":"object","properties":{"path":{"type":"string"}},"required":["path"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"content":{"type":"string"}},"required":["content"],"additionalProperties":false}}]}],"limits":{"max_steps":6,"max_model_calls":3},"conventions":[]}
```
</details>
