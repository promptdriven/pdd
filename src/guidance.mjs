// Generated from prompts/cli/guidance.prompt.md (sha256: 1ee1e80207cf7c886aeb48ff9ef89d0aadf028f61bf8d467d66494dd71904813).
import { readFileSync, readdirSync, lstatSync } from 'node:fs';
import { join, resolve } from 'node:path';

const shellQuote = value => "'" + value.replace(/'/g, "'\\''") + "'";

function markdownFiles(directory) {
  let info;
  try { info = lstatSync(directory); } catch (error) { if (error.code === 'ENOENT') return []; throw error; }
  if (!info.isDirectory() || info.isSymbolicLink()) throw Error('Guidance directory is not regular');
  return readdirSync(directory, { withFileTypes: true })
    .sort((a, b) => a.name < b.name ? -1 : a.name > b.name ? 1 : 0)
    .flatMap(entry => {
      const file = join(directory, entry.name);
      if (entry.isSymbolicLink()) throw Error('Guidance links are not loaded');
      return entry.isDirectory() ? markdownFiles(file) : entry.isFile() && entry.name.endsWith('.md') ? [file] : [];
    });
}
export function loadGuidance({ packageRoot, cwd }) {
  const files = [join(packageRoot, 'docs/prompting-guide.md'), join(packageRoot, 'skills/pdd/SKILL.md'),
    ...markdownFiles(join(packageRoot, 'skills/pdd/references'))];
  const command = [process.execPath, resolve(packageRoot, 'bin/pdd.mjs')];
  const sections = files.map(file => {
    if (!lstatSync(file).isFile() || lstatSync(file).isSymbolicLink()) throw Error('Guidance file is not regular');
    return `\n--- ${file} ---\n\n${readFileSync(file, 'utf8')}\n`;
  });
  return ['# PDD Alpha conversation guidance', `Package root: ${packageRoot}`, `Current project: ${cwd}`,
    'Read the ENTIRE Prompting guide below before ANY Story drafting. First summarize its relevant method, then follow the skill and manual recipes.',
    'Respect the current project instructions loaded normally by your native agent. Recipe files and pdd session provide manual guidance. For explicit workflow run/resume, follow the local runner’s current-stage instructions; that runner owns progression and PR steps.',
    `Exact installed PDD argv prefix: ${JSON.stringify(command)}`,
    `For every PDD command use this absolute executable prefix: ${command.map(shellQuote).join(' ')}. Append only the normal documented PDD arguments. Native tool login shells may resolve bare pdd to an older/private installation; do not use that other installation. Do not change PATH, shell profiles, native settings or credentials to work around it. This prefix grants no additional action authority.`,
    ...sections].join('\n\n');
}
