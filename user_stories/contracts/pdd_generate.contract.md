<!-- pdd-story-contract derived-from-story="../story__pdd_generate.md" story-hash="de0a7b28c908d6af" issue-ref="https://github.com/promptdriven/pdd/issues/1703" -->

# Contract: pdd generate

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_generate.md`), not this contract.

## Covers

- R1: Standard prompt-file generation creates code from an explicit prompt or template request.
- R2: Agentic issue generation routes GitHub issue URLs to the architecture workflow.
- R3: Incremental PRD generation requires explicit `--incremental --experimental-prd` opt-in.
- R4: Mode-specific guardrails reject ambiguous or unsupported flag combinations.
- R5: Estimate mode previews standard generation cost without writing outputs or running providers.

## Context

The `pdd generate` command is implemented by
`prompts/commands/generate_python.prompt`. It owns the top-level generate
surface for standard prompt-file generation, template-based generation, GitHub
issue architecture generation, incremental PRD propagation, snapshot context,
prompt-checkup gating, and estimate-mode routing.

## Acceptance Criteria

1. Given a prompt file and no template, when the user runs `pdd generate`, then the command validates the request and invokes standard code generation with the resolved prompt, output, environment, snapshot, and prompt-checkup options.
2. Given a template name and no prompt file, when the user runs `pdd generate --template <name>`, then the command resolves the template and invokes standard generation without requiring a separate prompt file.
3. Given both a prompt file and `--template`, when the user runs `pdd generate`, then the command rejects the ambiguous request before any generation workflow starts.
4. Given a GitHub issue URL without incremental PRD flags, when the user runs `pdd generate <issue-url>`, then the command routes to the agentic architecture workflow and forwards project-root, prompt-skip, GitHub-state, and output-directory choices.
5. Given a PRD-like source or issue URL with `--incremental --experimental-prd`, when the user runs `pdd generate`, then the command routes to incremental PRD propagation and distinguishes dry-run output from files actually written.
6. Given `--incremental` on a PRD-like source without `--experimental-prd`, when the user runs the command, then PDD raises a usage error that tells the user how to opt in explicitly.
7. Given global estimate mode for standard prompt-file generation, when the user runs `pdd --estimate generate`, then PDD returns an estimate payload without writing command outputs, evidence manifests, or cost rows for a real run.

## Oracle

These details matter for pass/fail:
- standard prompt-file and template routing
- prompt-file/template mutual exclusion
- GitHub issue URL routing to architecture generation
- explicit incremental PRD opt-in and dry-run labeling
- mode-specific rejection for unsupported flags such as standard-mode `--project-root`, non-PRD `--dry-run`, and unsupported `--snapshot-context`
- estimate mode staying side-effect-free for standard generation
- prompt-checkup gate forwarding before downstream generation

## Non-Oracle

These details should not matter:
- exact generated code or architecture content
- exact console color/style
- exact model/provider selected during real generation
- exact wording of non-user-facing helper messages
- internal function names below the public workflow boundary

## Negative Cases

- A request with both a prompt file and `--template` must not proceed to generation.
- `--dry-run` must not be accepted outside incremental PRD mode.
- A PRD-like source with `--incremental` must not silently route to PRD propagation without `--experimental-prd`.
- Agentic or incremental multi-step generation must not claim support for standard estimate mode.
- Mode-specific flags such as `--project-root` and `--snapshot-context` must not be silently ignored on unsupported paths.

## Non-Goals

- This story does not verify the generated artifact contents.
- This story does not cover `pdd test` or `pdd example`.
- This story does not prescribe the internal architecture workflow step sequence.

## Candidate Prompts

- `prompts/commands/generate_python.prompt` — primary owner of the `pdd generate` CLI.
- `prompts/code_generator_main_python.prompt` — related standard prompt-file generation workflow.
- `prompts/agentic_architecture_python.prompt` — related GitHub issue architecture workflow.
- `prompts/incremental_prd_architecture_python.prompt` — related incremental PRD workflow.
- `prompts/prompt_gate_python.prompt` — related prompt-checkup gate support.

## Notes

This story seeds the #1703 top-flow regression backfill for the documented
`pdd generate` entry point.
