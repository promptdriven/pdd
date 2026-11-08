// Generated from prompts/cli/workflow-setup.prompt.md (sha256: 37195d39837196bbf574fe3fb24de8fab1765a62ffcb084e39ba94e67ccc22fe).
import { checkWorkflowAgents } from './workflow-agents.mjs';

const recovery = 'Agent readiness could not be checked. Run codex login status, claude auth status, gemini --version or agy models. gemini --version does not verify sign-in.';
export async function setupWithWorkflowAgent({ cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  const stderr = ports.stderr ?? process.stderr;
  if (typeof ports.setup !== 'function') {
    stderr.write('The setup action is unavailable. Run setup again from a complete PDD package.\n');
    return 1;
  }
  let selected;
  try { selected = await (ports.checkWorkflowAgents ?? checkWorkflowAgents)({ cwd, env }, ports); }
  catch { stderr.write(`${recovery}\n`); return 1; }
  if (!selected.ok) { stderr.write(`${selected.message || recovery}\n`); return 1; }
  if (typeof selected.hint === 'string' && selected.hint) stderr.write(`${selected.hint}\n`);
  try {
    const code = await ports.setup({ agent: selected.agent, cwd, env });
    if (Number.isInteger(code) && code >= 0 && code <= 255) return code;
  } catch { /* Setup may already have effects. Do not retry or expose private data. */ }
  stderr.write('Setup did not report a valid result. Inspect the setup files before running setup again.\n');
  return 1;
}
