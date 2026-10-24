# Local workflow stage definitions

Own the compatibility bundled stage descriptions exported as `WORKFLOW_STAGES` by `src/workflow-definitions.mjs`. The editable JSON files are the canonical bundled stage definitions; derive this export through the definition loader so this module does not duplicate their schema or stage ordering. These describe local CLI orchestration, not a hosted model execution service. Each step keeps its bundled Markdown instruction filename and semantic identity. The runner consumes these definitions; no parser or native launcher policy lives here.

| Workflow | Ordered stages (`agent`, `human`, `pr`, `merge`) |
| --- | --- |
| feature | understand agent; visual optional agent; prompt-story agent; check agent; try optional agent; approve human; prompt-pr optional pr; prompt-merge merge of prompt-pr; build agent; verify agent; code-pr pr; code-merge merge of code-pr |
| bug | reproduce agent; prompt-story agent; check agent; try optional agent; approve human; prompt-pr optional pr; prompt-merge merge of prompt-pr; build agent; verify agent; code-pr pr; code-merge merge of code-pr |
| small-change | scope agent; change agent; verify agent; open-pr pr; wait-merge merge of open-pr |

These are 12/11/5 listed steps and at most 7/6/3 native agent sessions; feature and bug each have five mandatory agent stages. Optional steps remain listed even when skipped. Human decisions, PR operations and merge observations do not launch agents. Each stage exposes `id`, `kind`, `file` (its id plus `.md`), optional `optional:true`, and for merge stages `prStage`. Definitions and entries are frozen against caller mutation. The compatibility export retains these three bundled names. Runtime run/list selection uses loader discovery and accepts arbitrary valid project or bundled names; this export must not restrict that selection. Do not add implicit executable step types.

## Dependencies

The bundled `.pdd/workflows/{feature,bug,small-change}/` Markdown supplies stage instructions at runtime. Load each bundled workflow.json and its declared Markdown through [the definition loader](workflow-definition-loader.prompt.md), a required runtime dependency. This module performs no Git, native or publication effects. Semantic protocol/approval/publication/dependency fields belong to the loader schema, rather than hardcoded stage-name checks.
