# Draft missing Runtime interfaces

Own `src/interface-draft.mjs`. Preserve prompt prose and all existing blocks. Export `runInterfaceDraft({words,all,json,cwd}, ports)`, `interfaceFindings({root,paths})`, `runtimeCoverage({root,paths})`, `missingInterfaces(root)` and `runAutomaticApproval({path,root,tests}, ports)`.

Draft only Git-visible regular in-repository prompt files in the runtime workspace. Resolve explicit paths from cwd. Refuse unsafe paths, malformed blocks, unknown paths and --all combined with paths before any write. With --all select all workspace prompts, excluding nested fixture projects. Without --all require at least one path. Continue across independent draft failures and report each result. Never overwrite a block or choose native-only for the user.

Infer entry names and complete input/result schemas from explicit JSON interface declarations in the prompt or declared schema/contract dependencies. Resolve contract references with the shared contract reader. Existing module exports may supply clear operation names, but never invent types from names. No AI, authentication, program execution or network. If a complete declaration cannot be derived, write a partial draft with available operations and explicit draft gaps. Gaps refuse local lint and automatic approval. Do not manufacture empty schemas to report success. Keep the prose bytes unchanged. Fill the draft's prose hash after insertion. Store drafting provenance under .pdd/, outside Git: original prose, draft interface and Git head identities. These are evidence, not approval.

Lint every selected block locally through preflight and shared contract expansion. Return per-path state (drafted, existing or refused), problems and lint_clean. Print drafted, existing, lint-clean and refused counts. JSON contains the same results and exit_code. Exit 0 only when every selected block lints clean; exit 4 for block or drafting problems; exit 2 for usage/repository/path problems. Drafts are not approved.

Automatic approval accepts only a complete full draft made by this command whose committed prose and all existing source still match its provenance. Reject native-only, partial, gaps, an edited interface, new prose and strict approval mode. Require a native test command that names existing committed tests; run it from the repository through the execution port. Require exit 0 and then a complete prompt check on every existing Story test that reaches this prompt, using the normal runtime client. No missing tests, cached passes, unknown/not-run/refused rows, partial checks or absent passing counts qualify. Recheck source identities after both runs. Evidence includes command, native exit, current source and prose hashes, prompt-check rows and route automatic-check-pass. Use the shared approval writer only after this evidence is complete; roll back a prompt write if journal recording fails. Never convert this to a person's approval or call it from draft/setup. Prompt and native checks remain separate evidence.

## Dependencies

- [Preflight](runtime-preflight.prompt.md): required for block discovery, source hashing, schemas and test discovery.
- [Contract references](contract-refs.prompt.md): required for expanding declared schema references.
- [Runtime client](runtime-client.prompt.md): required for complete prompt-check evidence.
- [Prompt approval](prompt-approve.prompt.md): required for safe status editing and path validation.
- [Approval policy](approval-policy.prompt.md): required for strict mode and evidence recording.
- [Runtime workspace](runtime-workspace.prompt.md): required for selecting project source and excluding fixtures.
