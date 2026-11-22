// Generated from prompts/cli/human-boundary-card.prompt.md (sha256: 298d633397532c9d24801ff1c9a34153d62bf374707ff04c5bb43cd1a8f5d36f).
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
