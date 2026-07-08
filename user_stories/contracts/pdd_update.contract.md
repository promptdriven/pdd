<!-- pdd-story-contract derived-from-story="../story__pdd_update.md" story-hash="9c6a941b9c3e3f96" issue-ref="https://github.com/promptdriven/pdd/issues/1703" -->

# Contract: pdd update

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_update.md`), not this contract.

## Covers

- R1: Repository-wide update scans changed code/prompt pairs and updates prompts in batch.
- R2: Single-code regeneration mode derives or creates the prompt path for a changed code file.
- R3: Git and manual true-update modes update an existing prompt from modified code.
- R4: CLI validation rejects ambiguous update modes and incompatible options before work starts.
- R5: Metadata synchronization and fingerprint finalization keep prompt/code state consistent after successful updates.

## Context

The `pdd update` command is exposed through
`prompts/commands/modify_python.prompt` and implemented by
`prompts/update_main_python.prompt`. It back-propagates code changes into the
authoritative prompt, either for a single target or across a repository.

## Acceptance Criteria

1. Given no file arguments or `--all`, when the user runs `pdd update`, then the command scans the repository for changed code/prompt pairs, filters unsupported files, updates eligible prompts, and reports per-pair status.
2. Given one modified code file, when the user runs `pdd update <code-file>`, then the command resolves or creates the corresponding prompt path and performs regeneration-mode prompt update.
3. Given two files with `--git`, when the user runs `pdd update --git <prompt> <modified-code>`, then the command updates the prompt by comparing the modified code against Git history.
4. Given three files without `--git`, when the user runs `pdd update <prompt> <modified-code> <original-code>`, then the command updates the prompt from the explicit original/modified code pair.
5. Given incompatible options such as `--all` with file paths, `--output` in repo mode, or file-mode-only arguments with repo-mode filters, when the user invokes the command, then PDD rejects the request before running update logic.
6. Given `--sync-metadata`, when an update succeeds, then PDD runs metadata synchronization and exits non-zero if any required metadata stage fails.
7. Given a successful single-file or regeneration update without redirected output, when the command returns, then PDD clears stale run reports and finalizes the affected prompt/code fingerprint unless a documented skip condition applies.

## Oracle

These details matter for pass/fail:
- routing among repo-wide, regeneration, git true-update, and manual true-update modes
- option validation before update logic
- agentic-first update with legacy fallback where available
- per-target `.pddrc` runtime config resolution in repo mode
- metadata-sync failure causing non-zero exit when requested
- default fingerprint finalization after successful single-file/regeneration updates
- stale run-report cleanup before writing fresh fingerprints

## Non-Oracle

These details should not matter:
- exact prompt prose produced by the updater
- exact model/provider selected during real update
- exact progress bar or Rich table styling
- exact ordering of repo-mode pairs beyond deterministic reporting where required
- internal helper names below the public workflow boundary

## Negative Cases

- Two file arguments must not be accepted without `--git`.
- Three file arguments must not be accepted with `--git`.
- Repo mode must not accept `--output`, `--git`, or file paths.
- File modes must not accept repo-only filters such as `--extensions`, `--directory`, non-default `--base-branch`, `--dry-run`, or `--budget`.
- A metadata-sync failure must not be swallowed as a successful `pdd update --sync-metadata` run.
- A fresh fingerprint must not be written while a stale run report for the same prompt/code identity remains.

## Non-Goals

- This story does not verify the exact updated prompt contents.
- This story does not cover `pdd change` or `pdd sync`.
- This story does not prescribe the internal agent implementation.

## Candidate Prompts

- `prompts/commands/modify_python.prompt` — primary owner of the `pdd update` CLI surface.
- `prompts/update_main_python.prompt` — primary owner of update routing and metadata finalization behavior.
- `prompts/agentic_update_python.prompt` — related agentic update implementation.
- `prompts/metadata_sync_python.prompt` — related metadata synchronization support.
- `prompts/operation_log_python.prompt` — related fingerprint and run-report metadata support.

## Notes

This story seeds the #1703 top-flow regression backfill for the documented
`pdd update` command.
