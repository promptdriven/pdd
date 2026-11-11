// Generated from prompts/cli/runtime-seam.prompt.md (sha256: 48a8d03f53fc3b9ef9244da7f60555c08d0edabc256eb939984aedfd18f87525).
import { dirname, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { runTry as runtimeRunTry } from './runtime/index.mjs';

const TRY_LAUNCHER_URL = pathToFileURL(join(dirname(fileURLToPath(import.meta.url)), 'try-doors.mjs')).href;

export function runTry(input, ports = {}) {
  return runtimeRunTry(input, { tryLauncherUrl: TRY_LAUNCHER_URL, ...ports });
}

export {
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
  createSavedStoryEvidenceReader,
  exactIntegerLeaves,
  findTests,
  gitFiles,
  interfaceBlocks,
  interfaceSchemaProblems,
  isSecretPath,
  isStoryPath,
  jsonSafe,
  loadInterfaceDraft,
  loadRuntimeClient,
  loadRuntimeWorkspace,
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
  sha256,
  sourceFilePort,
  storyLines,
  stringifyScenarioJson,
  withExactIntegers,
} from './runtime/index.mjs';
