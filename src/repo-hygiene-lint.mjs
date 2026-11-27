// Prompt: prompts/cli/repo-hygiene-lint.prompt.md
// Thin backwards-compatible Layer-1 facade delegating strictly to `src/core/lint/*.mjs` and `src/shared/glob-match.mjs`.
// Zero `autopilot/` imports, zero `runtime-seam` imports, zero prose-regex scrapers.
import { lintRepoProject } from './core/lint/project-lint.mjs';
export {
  lintRepoProject,
  runConfiguredLintCommands,
} from './core/lint/project-lint.mjs';
export const lintRepoAntiPatterns = (opts = {}) => lintRepoProject(opts).warnings;
export {
  loadProjectLintConfig,
} from './core/lint/project-config.mjs';
export {
  stripPromptMetadata,
  stripPromptMetadataPreservingLines,
  hasNativeOnlyFrontmatter,
  isNativeOnlyPrompt,
  extractFrontmatterPorts,
  extractDependencyLinks,
  extractDependencyLinkTargets,
  extractRelativeMarkdownLinks,
} from './core/lint/prompt-metadata.mjs';
export {
  collectMarkdownIntegrityFindings,
  lintPromptStructure,
} from './core/lint/prompt-rules.mjs';
export {
  compileGlobMatcher,
} from './shared/glob-match.mjs';
export {
  DEFAULT_SCENARIO_MAX_STEPS,
  DEFAULT_SCENARIO_MAX_WORLD_BYTES,
  computeDefaultScenarioCallCap,
  evaluateScenarioHygiene,
  collectScenarioHygieneFindings,
} from './core/lint/scenario-hygiene.mjs';
export {
  runLocalLint,
} from './core/lint/run-local-lint.mjs';
export {
  resolveLintScope,
} from './core/lint/lint-scope.mjs';
export {
  runDiffSpotlight,
  analyzeDiffEntries,
  findConflictMarkers,
} from './core/lint/test-inventory.mjs';
