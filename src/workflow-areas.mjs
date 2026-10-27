// Generated from prompts/cli/workflow-areas.prompt.md (sha256: f37aba928f978982e9ba909ebd7699cf643081c0713d2479a2bbbd874ab36a17).
import { existsSync, readFileSync, readdirSync } from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join, resolve } from 'node:path';

const WORD = /^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/;
const word = value => typeof value === 'string' && value.length <= 64 && WORD.test(value);

function projectRoot(cwd) {
  if (typeof cwd !== 'string' || !cwd) return null;
  for (let folder = resolve(cwd); ; folder = dirname(folder)) {
    if (existsSync(join(folder, '.git'))) return folder;
    if (dirname(folder) === folder) return null;
  }
}

// The skill folders in lookup order; the first pdd-NAME/workflow.json found wins.
function skillRoots({ packageRoot, cwd, home = homedir() }) {
  const project = projectRoot(cwd);
  return [...(project ? [[join(project, '.agents', 'skills'), 'project'], [join(project, '.claude', 'skills'), 'project']] : []),
    ...(home ? [[join(home, '.agents', 'skills'), 'home'], [join(home, '.claude', 'skills'), 'home']] : []),
    [join(packageRoot, 'skills'), 'package']];
}

function parse(name, file) {
  const invalid = why => Object.assign(Error(`The ${name} workflow in ${file} is not valid: ${why}.`), { code: 'workflow_invalid' });
  let data;
  try { data = JSON.parse(readFileSync(file, 'utf8')); } catch { throw invalid('workflow.json is not readable JSON'); }
  if (data?.version !== 2 || !Array.isArray(data.areas) || !data.areas.length) throw invalid('it needs version 2 and at least one area');
  return data.areas.map((area, index) => {
    const last = index === data.areas.length - 1;
    const askCode = !last && area?.gate === 'pr' && area.then === 'ask-code';
    if (!word(area?.name) || !Array.isArray(area.steps) || !area.steps.length || !area.steps.every(word)
      || !Array.isArray(area.optional ?? []) || !(area.optional ?? []).every(step => area.steps.includes(step))
      || !(last ? area.gate === 'pr' && area.then === undefined : area.gate === 'approve' && area.then === undefined || askCode))
      throw invalid(`area ${index + 1} needs a name, steps, optional steps from its steps and gate ${last ? '"pr"' : '"approve", or "pr" with "then":"ask-code"'}`);
    return { name: area.name, steps: [...area.steps], optional: [...(area.optional ?? [])], gate: area.gate, ...(askCode ? { then: 'ask-code' } : {}) };
  });
}

function found(options) {
  const workflows = new Map();
  for (const [root, source] of skillRoots(options)) {
    let entries;
    try { entries = readdirSync(root, { withFileTypes: true }); } catch { continue; }
    for (const entry of entries.sort((a, b) => a.name.localeCompare(b.name))) {
      const name = entry.name.slice(4), dir = join(root, entry.name);
      if (!entry.name.startsWith('pdd-') || !word(name) || workflows.has(name) || !existsSync(join(dir, 'workflow.json'))) continue;
      // A copy that pdd installed (it has pdd's marker) is not an override: the running package is newer or the same.
      if (source === 'home' && existsSync(join(dir, '.pdd-skill.json'))) continue;
      workflows.set(name, { name, skill: entry.name, dir, source });
    }
  }
  return workflows;
}

export function readWorkflowAreas({ packageRoot, name, cwd, home }) {
  if (!word(name)) throw Object.assign(Error(`"${String(name).slice(0, 64)}" is not a workflow name.`), { code: 'workflow_unknown' });
  const workflows = found({ packageRoot, cwd, home }), workflow = workflows.get(name);
  if (!workflow) throw Object.assign(Error(`There is no ${name} workflow. Workflows: ${[...workflows.keys()].sort().join(', ') || 'none'}.`), { code: 'workflow_unknown' });
  return { ...workflow, areas: parse(name, join(workflow.dir, 'workflow.json')) };
}

export function listWorkflowAreas({ packageRoot, cwd, home }) {
  return [...found({ packageRoot, cwd, home }).values()].sort((a, b) => a.name.localeCompare(b.name))
    .map(workflow => ({ ...workflow, areas: parse(workflow.name, join(workflow.dir, 'workflow.json')) }));
}

export function formatWorkflowList(list, { json = false } = {}) {
  if (json) return JSON.stringify({ workflows: list.map(({ name, skill, source, dir, areas }) => ({ name, skill, source, dir, areas })), default: null });
  const lines = list.length ? list.map(({ name, areas, source }) => `${name}  ${areas.map(area =>
    `${area.name} [${area.steps.map(step => area.optional.includes(step) ? `${step}?` : step).join(', ')}] → ${area.gate}`).join(' → ')}  (${source ?? 'package'})`)
    : ['No workflows found.'];
  lines.push('Listing starts no work. Use pdd workflow run NAME ISSUE.');
  return lines.join('\n');
}
