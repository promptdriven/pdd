// Generated from prompts/cli/workflow-setup.prompt.md (sha256: 18143e3f5385068b9659cdb0fbaa9d2891072566a5ae580db4cf4525874973cf).
import { checkWorkflowAgents } from './workflow-agents.mjs';

const recovery = 'Agent sign-in could not be checked. Run codex login status or claude auth status.';
export async function setupWithWorkflowAgent({ cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  const stderr = ports.stderr ?? process.stderr;
  if (typeof ports.setup !== 'function') {
    stderr.write('The setup action is unavailable. Run setup again from a complete PDD package.\n');
    return 1;
  }
  let selected;
  try { selected = await checkWorkflowAgents({ cwd, env }, ports); }
  catch { stderr.write(`${recovery}\n`); return 1; }
  if (!selected.ok) { stderr.write(`${selected.message}\n`); return 1; }
  try {
    const code = await ports.setup({ agent: selected.agent, cwd, env });
    if (Number.isInteger(code) && code >= 0 && code <= 255) return code;
  } catch { /* Setup may already have effects. Do not retry or expose private data. */ }
  stderr.write('Setup did not report a valid result. Inspect the setup files before running setup again.\n');
  return 1;
}
