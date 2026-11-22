// Generated from prompts/cli/autopilot-validator.prompt.md (sha256: 018c8e6b0791b1584546828de6e955e4b4bd0dc2ffa4a2f8538512cb118f3de2).
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
