// Generated from prompts/cli/workflow-areas.prompt.md (sha256: 8d90e2359e309d8e082345aace26e14483ac9a3498744529806b259f3023c95a).
import { existsSync, readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';

const WORD = /^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/;
const word = value => typeof value === 'string' && value.length <= 64 && WORD.test(value);
const invalid = (name, why) => Object.assign(Error(`The ${name} workflow is not valid: ${why}.`), { code: 'workflow_invalid' });

export function readWorkflowAreas({ packageRoot, name }) {
  if (!word(name)) throw Object.assign(Error(`"${String(name).slice(0, 64)}" is not a workflow name.`), { code: 'workflow_unknown' });
  const skill = `pdd-${name}`;
  let data;
  try { data = JSON.parse(readFileSync(join(packageRoot, 'skills', skill, 'workflow.json'), 'utf8')); }
  catch (error) {
    if (error.code === 'ENOENT') {
      const known = workflowNames(packageRoot).filter(other => existsSync(join(packageRoot, 'skills', `pdd-${other}`, 'workflow.json')));
      throw Object.assign(Error(`There is no ${name} workflow. Workflows: ${known.join(', ') || 'none'}.`), { code: 'workflow_unknown' });
    }
    throw invalid(name, 'workflow.json is not readable JSON');
  }
  if (data?.version !== 2 || !Array.isArray(data.areas) || !data.areas.length) throw invalid(name, 'it needs version 2 and at least one area');
  const areas = data.areas.map((area, index) => {
    const last = index === data.areas.length - 1;
    if (!word(area?.name) || !Array.isArray(area.steps) || !area.steps.length || !area.steps.every(word)
      || !Array.isArray(area.optional ?? []) || !(area.optional ?? []).every(step => area.steps.includes(step))
      || area.gate !== (last ? 'pr' : 'approve')) throw invalid(name, `area ${index + 1} needs a name, steps, optional steps from its steps and gate ${last ? 'pr' : 'approve'}`);
    return { name: area.name, steps: [...area.steps], optional: [...(area.optional ?? [])], gate: area.gate };
  });
  return { name, skill, areas };
}

function workflowNames(packageRoot) {
  let entries;
  try { entries = readdirSync(join(packageRoot, 'skills'), { withFileTypes: true }); }
  catch (error) { if (error.code === 'ENOENT') return []; throw error; }
  return entries.filter(entry => entry.isDirectory() && entry.name.startsWith('pdd-')).map(entry => entry.name.slice(4)).filter(word).sort();
}

export function listWorkflowAreas({ packageRoot }) {
  return workflowNames(packageRoot).filter(name => existsSync(join(packageRoot, 'skills', `pdd-${name}`, 'workflow.json')))
    .map(name => readWorkflowAreas({ packageRoot, name }));
}

export function formatWorkflowList(list, { json = false } = {}) {
  if (json) return JSON.stringify({ workflows: list.map(({ name, skill, areas }) => ({ name, skill, areas })), default: null });
  const lines = list.length ? list.map(({ name, areas }) => `${name}  ${areas.map(area =>
    `${area.name} [${area.steps.map(step => area.optional.includes(step) ? `${step}?` : step).join(', ')}] → ${area.gate}`).join(' → ')}`)
    : ['No workflows found.'];
  lines.push('Listing starts no work. Use pdd workflow run NAME ISSUE.');
  return lines.join('\n');
}
