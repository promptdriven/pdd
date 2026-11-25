// Prompt: prompts/cli/autopilot-validator.prompt.md

// Backwards-compatible Layer-2 facade re-exporting all public validator symbols.
export {
  MIN_REALISTIC_PAYLOAD_BYTES,
  REAL_HOST_FAILURE_CLASSES,
  canonicalTargetPath,
  detectChangedSurfaces,
  detectNativeOnlyModules,
} from './autopilot/validator/surfaces.mjs';

export {
  MAX_VALIDATION_REPAIRS,
  checkCapabilityRequirements,
  evaluateValidationOutcome,
  formatHumanVerificationCard,
  planValidationResume,
  shouldClaimWithCooldowns,
} from './autopilot/validator/policy.mjs';

export {
  collectTestFixedSleepFindings,
  collectTestUnexcusedSkipFindings,
  lintAutopilotTestHygiene,
  lintChangedTestPrivateImports,
  lintRepoValidationBackside,
  lintTestFixedSleeps,
  lintTestHygiene,
  lintTestUnexcusedSkips,
  lintValidationCode,
  lintValidationSkips,
  maskStringsPreserveLines,
  scanJsPreserveLines,
  stripCommentsPreserveLines,
} from './autopilot/validator/test-probes.mjs';
