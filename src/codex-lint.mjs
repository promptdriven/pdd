// Backwards-compatible facade for `src/autopilot/ai-lint.mjs` (zero runtime-seam imports).
export {
  buildAiLintPrompt,
  buildCodexLintPrompt,
  groupAiLintBatches,
  groupCodexLintBatches,
  runAiLint,
  runCodexLint,
} from './autopilot/ai-lint.mjs';
