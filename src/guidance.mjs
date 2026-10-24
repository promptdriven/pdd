// Generated from prompts/cli/guidance.prompt.md (sha256: 3f5107fe1a3b708c6c9e59526169d7190beb3f925d4cb612e74abf1b75a42086).
import { readFileSync, readdirSync, lstatSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { BUNDLED_WORKFLOW_NAMES } from './command-catalog.mjs';

const shellQuote = value => "'" + value.replace(/'/g, "'\\''") + "'";

function markdownFiles(directory, required = false) {
  let info;
  try { info = lstatSync(directory); } catch (error) { if (!required && error.code === 'ENOENT') return []; throw error; }
  if (!info.isDirectory() || info.isSymbolicLink()) throw Error('Guidance directory is not regular');
  return readdirSync(directory, { withFileTypes: true })
    .sort((a, b) => a.name < b.name ? -1 : a.name > b.name ? 1 : 0)
    .flatMap(entry => {
      const file = join(directory, entry.name);
      if (entry.isSymbolicLink()) throw Error('Guidance links are not loaded');
      return entry.isDirectory() ? markdownFiles(file) : entry.isFile() && entry.name.endsWith('.md') ? [file] : [];
    });
}
export function loadGuidance({ packageRoot, cwd, workflows = false, workflowName }) {
  if (workflowName !== undefined && !BUNDLED_WORKFLOW_NAMES.includes(workflowName)) throw Error('Unknown bundled recipe');
  const files = [join(packageRoot, 'docs/prompting-guide.md'), join(packageRoot, 'skills/pdd/SKILL.md'),
    ...markdownFiles(join(packageRoot, 'skills/pdd/references'))];
  if (workflows) {
    const directory = workflowName ? join(packageRoot, '.pdd/workflows', workflowName) : join(packageRoot, '.pdd/workflows');
    const recipes = markdownFiles(directory, true);
    if (!recipes.length) throw Error('Bundled recipes are missing');
    const selectedEntry = workflowName ? join(directory, 'WORKFLOW.md') : null;
    files.push(join(packageRoot, 'docs/workflows.md'),
      ...(selectedEntry ? [selectedEntry, ...recipes.filter(file => file !== selectedEntry)] : recipes));
  }
  const command = [process.execPath, resolve(packageRoot, 'bin/pdd.mjs')];
  const sections = files.map(file => {
    if (!lstatSync(file).isFile() || lstatSync(file).isSymbolicLink()) throw Error('Guidance file is not regular');
    return `\n--- ${file} ---\n\n${readFileSync(file, 'utf8')}\n`;
  });
  return ['# PDD Alpha conversation guidance', `Package root: ${packageRoot}`, `Current project: ${cwd}`,
    'Read the ENTIRE Prompting guide below before ANY Story drafting. First summarize its relevant method, then follow the skill and manual recipes.',
    'Respect the current project instructions loaded normally by your native agent. Recipe files and pdd session provide manual guidance. For explicit workflow run/resume, follow the local runner’s current-stage instructions; that runner owns progression and PR steps.',
    ...(workflowName ? [`Selected bundled workflow: ${workflowName}. Choose this provided recipe and follow its WORKFLOW.md and supplied steps after the guide summary. When used as a direct conversation shortcut, this selects one native conversation; explicit workflow run/resume instead follows its runner-owned stages and PR steps.`] : []),
    `Exact installed PDD argv prefix: ${JSON.stringify(command)}`,
    `For every PDD command use this absolute executable prefix: ${command.map(shellQuote).join(' ')}. Append only the normal documented PDD arguments. Native tool login shells may resolve bare pdd to an older/private installation; do not use that other installation. Do not change PATH, shell profiles, native settings or credentials to work around it. This prefix grants no additional action authority.`,
    ...sections].join('\n\n');
}
