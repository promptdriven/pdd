// Generated from prompts/cli/workflow-definitions.prompt.md (sha256: 788d86597f1c2c87df54fde2d34d7f721c3212d187106f2ff57526cfea03f86f).
import { fileURLToPath } from 'node:url';
import { loadWorkflowDefinition } from './workflow-definition-loader.mjs';
const packageRoot = fileURLToPath(new URL('../', import.meta.url));
export const WORKFLOW_STAGES = Object.freeze(Object.fromEntries(
  ['feature', 'bug', 'small-change'].map(name => [name,
    loadWorkflowDefinition({ name, cwd: packageRoot, packageRoot }).stages])));
