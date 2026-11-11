# Follow the current PDD instructions

As a person installing and using PDD, I want its guides and installed project instructions to describe the available tools and steps, so that I can follow them without guessing.

## Acceptance criteria

1. Running `pdd setup` writes a short project block that names all ten bundled skills and lists feature, bug, small-change, product and custom workflow names.
2. The usage guide describes Gemini Try support by the five required help options and shows the missing-option error, without requiring a particular Gemini CLI version.
3. The guides agree on skill installation and updates, distinguish the setup skill from the setup command, and list the MCP entries to remove when uninstalling.
4. The custom-workflow example shows `mybug` in the workflow list, and the skills table includes the dependency graph skill.

## What must not change

Keep the setup block within ten lines, preserve the person's surrounding project instructions, and keep repeated setup idempotent. Agent selection and Gemini capability checks retain their existing behavior. Leave the RUNBOOK and Prompting guide files unchanged.

## Verification

The setup integration test exercises the emitted project instructions and repeated setup through the CLI. Existing skill, command-reference, agent-adapter and workflow tests cover the related contracts. Guide wording is checked against the current implementation; it has no executable Runtime entry point.
