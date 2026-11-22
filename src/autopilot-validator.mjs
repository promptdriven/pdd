// Generated from prompts/cli/autopilot-validator.prompt.md (sha256: 75fde4547979ce8f760b5cb49996fe40b92c8567837622ceac4c2dd1c41f41ce).
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
