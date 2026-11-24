// Prompt: prompts/cli/autopilot-validator.prompt.md

// Layer-2 facade re-exporting the shared Layer-1 polyglot test runner registry (#3561, #3151).
export {
  TEST_RUNNERS,
  TEST_RUNNER_KINDS,
  buildRunnerEnv,
  buildRunnerInvocation,
  detectTestRunner,
  extractTestCases,
  normalizeRunnerKind,
  parseCargoReport,
  parseGoJsonReport,
  parseJunitXml,
  parsePytestVerboseReport,
  parseTapReport,
  parseTestSummaryOutput,
  parseVitestVerboseReport,
  resolvePytestBinary,
} from '../../core/polyglot-runners.mjs';
