// Generated from prompts/cli/autopilot-validator.prompt.md (sha256: 691dd6196bed4cd3f73c6e54357b81dbbd926f01249066f198c14749055ad53b).
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
  MOCK_USAGE_RE,
  REAL_E2E_EXEC_RE,
  collectTestFixedSleepFindings,
  collectTestUnexcusedSkipFindings,
  detectRealE2eKindsInTest,
  detectRealHostProbesInTest,
  inspectTestBoundaryTargets,
  lintAutopilotTestHygiene,
  lintBoundaryMockOnlyTests,
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
