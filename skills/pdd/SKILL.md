---
name: pdd
description: Use PDD to define software behavior in prompts, check prompt changes, try a proposed behavior when supported, and follow a PDD workflow. Use when a person asks for PDD or prompt-first work; ordinary coding does not require this skill.
---

# PDD

PDD keeps the behavior contract in readable prompts beside the code. Follow the person's request, inspect the repository's guidance, and use only commands shown by `pdd --help` for the installed version. Do not claim a command, check, preview, or runtime result that did not happen.

Read the [Prompting guide](../../docs/prompting-guide.md) before writing or substantially changing prompts. Keep one canonical prompt for each owned module, describe behavior and its important boundaries, and link required contracts from the prompt's Dependencies section. Treat a prompt as a contract, not a copy of the implementation.

Choose a workflow from the repository's `.pdd/workflows/` directory when one fits. The public recipes in this repository are [feature](../../.pdd/workflows/feature/WORKFLOW.md), [bug](../../.pdd/workflows/bug/WORKFLOW.md), and [small change](../../.pdd/workflows/small-change/WORKFLOW.md). Follow every linked step in order and state clearly when a supported step is unavailable.

Keep authored expectations separate from observed results. A model answer is not an expected result. A prompt check does not prove generated code; code tests do not prove that a prompt expresses the intended rule; formal analysis covers only its declared assumptions and scope. Report the evidence actually collected and its limits.

When prompt behavior changes, show the current prompt and Story for the person's review. The feature and bug recipes use `approval: story`, `publish-prompt-pr`, and `wait-for-merge: pr1` for the person's approval and Prompt PR handoff before code work. After code tests, `publish-code-pr` and `wait-for-merge: pr2` publish the Code PR and leave its merge to the person. Follow those stages when supported by the installed release. A small contained change may use one PR without adopting or rewriting prompt space; see the small-change workflow.

Try is optional. Recommend it when the changed behavior benefits from a person exercising the proposed flow, and use it only when the installed PDD distribution supports it. If unavailable, say so; never describe a draft, link, or unavailable run as a completed Try.

The built PDD runtime is a separate package. It is free to use with PDD and may not be copied or resold. This source repository does not contain its implementation or private schemas. Availability and supported features depend on the installed release.

For setup, phone access, command discovery, prompt sessions, workflows, and evidence, use the [user documentation](../../docs/index.md).
