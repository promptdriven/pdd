// Prompt: prompts/cli/repo-hygiene-lint.prompt.md
// Thin backwards-compatible Layer-1 facade delegating strictly to `src/core/lint/*.mjs`.
// Zero `autopilot/` imports, zero `runtime-seam` imports, zero JS code-test regex noise.
export {
  lintRepoProject,
  runConfiguredLintCommands,
} from './core/lint/project-lint.mjs';
export {
  MAX_CUSTOM_RULES,
  evaluateCustomRulesOnFile,
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
} from './core/lint/prompt-metadata.mjs';
export {
  DECLARATIVE_SCHEMA_FENCE_LANGS,
  lintPromptCodeBlocks,
  lintPromptSize,
  lintPromptStructure,
} from './core/lint/prompt-rules.mjs';
export {
  lintNativeOnlyContract,
} from './core/lint/native-only-contract.mjs';
export {
  lintNativeOnlyPortParity,
  collectNativeOnlyPortParityFindings,
} from './core/lint/native-port-parity.mjs';
export {
  compileGlobMatcher,
  isSafeRegexPattern,
  parseRegexSafe,
} from './core/lint/regex-safety.mjs';
export {
  runLocalLint,
} from './core/lint/run-local-lint.mjs';
export {
  runDiffSpotlight,
  analyzeDiffEntries,
  findExecutableOnlyMarkers,
  findConflictMarkers,
} from './core/lint/test-inventory.mjs';
