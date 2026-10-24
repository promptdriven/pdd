// Generated from prompts/cli/workflow-definitions.prompt.md (sha256: 6b97edf48ab8a97c69377041459eb671cad0d20eae249257c74c2da2b5883d78).
import { fileURLToPath } from 'node:url';
import { loadWorkflowDefinition } from './workflow-definition-loader.mjs';
const packageRoot = fileURLToPath(new URL('../', import.meta.url));
export const WORKFLOW_STAGES = Object.freeze(Object.fromEntries(
  ['feature', 'bug', 'small-change'].map(name => [name,
    loadWorkflowDefinition({ name, cwd: packageRoot, packageRoot }).stages])));
