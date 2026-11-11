// Generated from prompts/cli/runtime-seam.prompt.md (sha256: b167fbb9bebf73b0aecf8c406e6a9158155c362ffa874359f822d57d0cec3ee1).
import { dirname, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { runTry as runtimeRunTry } from './runtime/index.mjs';

const TRY_LAUNCHER_URL = pathToFileURL(join(dirname(fileURLToPath(import.meta.url)), 'try-doors.mjs')).href;

export function runTry(input, ports = {}) {
  return runtimeRunTry(input, { tryLauncherUrl: TRY_LAUNCHER_URL, ...ports });
}

export {
  DEFAULT_RUNTIME_URL,
  LIMITS,
  PROMPT_TESTS_LABEL,
  PROMPT_TESTS_WORDS,
  allowsRuntimePath,
  buildAgentInput,
  captureSource,
  causeText,
  checkInput,
  checkPlanResultLines,
  checkPlanResults,
  checkRuntimeHealth,
  cleanText,
  contractCoverage,
  coverageView,
  createSavedStoryEvidenceReader,
  exactIntegerLeaves,
  findTests,
  gitFiles,
  interfaceBlocks,
  interfaceSchemaProblems,
  isSecretPath,
  isStoryPath,
  jsonSafe,
  loadRuntimeWorkspace,
  missingInterfaces,
  outcomeText,
  parseScenarioJson,
  preflight,
  promptRefusal,
  promptSchemaRefusals,
  proseSha256,
  readPrompt,
  requireRuntimePath,
  resultOutcome,
  runAutomaticApproval,
  runCheck,
  runContracts,
  runInterfaceDraft,
  runJobs,
  runMcp,
  runShim,
  runtimeOrigin,
  sha256,
  sourceFilePort,
  storyLines,
  stringifyScenarioJson,
  withExactIntegers,
} from './runtime/index.mjs';
