// Generated from prompts/cli/human-boundary-card.prompt.md (sha256: 3bb2a85af2ef244d2ee46cad58826432be719ff36abf8893084d16b3da80f4ca).
import {
  TEST_SCHEMA,
  findTests,
  gitFiles,
  interfaceBlocks,
  parseScenarioJson,
  promptMarkdownTargets,
  readPrompt,
  storyCriteria,
} from './runtime-seam.mjs';
import { BOUNDARY_CARD_MAX_LINES, createHumanBoundaryCard } from './core/human-boundary-card-core.mjs';

const {
  buildHumanBoundaryCard,
  fitBoundaryLines,
  formatApproveBoundaryCard,
} = createHumanBoundaryCard({
  TEST_SCHEMA,
  findTests,
  gitFiles,
  interfaceBlocks,
  parseScenarioJson,
  promptMarkdownTargets,
  readPrompt,
  storyCriteria,
});

export { BOUNDARY_CARD_MAX_LINES, buildHumanBoundaryCard, fitBoundaryLines, formatApproveBoundaryCard };
