// Prompt: prompts/cli/codex-lint.prompt.md
// Backwards-compatible facade over `src/autopilot/ai-lint.mjs` (zero runtime-seam imports).
export {
  buildAiLintPrompt,
  buildCodexLintPrompt,
  groupAiLintBatches,
  groupCodexLintBatches,
  runAdaptiveAiLint,
  runAiLint,
  runCodexLint,
} from './autopilot/ai-lint.mjs';
