// Generated from prompts/cli/project-setup.prompt.md (sha256: 832ea686a2670273a127e0266c4be36908fd9ed101a6d5a5d77f5b4a42c14800).
import { existsSync, lstatSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const START = '<!-- pdd:start -->', END = '<!-- pdd:end -->';

function block(packageRoot) {
  const lines = readFileSync(join(packageRoot, 'skills/pdd-setup/SKILL.md'), 'utf8').split('\n');
  const start = lines.indexOf(START), end = lines.indexOf(END);
  if (start < 0 || end < start) throw Error('The pdd-setup skill has no PDD block.');
  const runbook = existsSync(join(packageRoot, 'RUNBOOK.md'));
  return lines.slice(start, end + 1).filter(line => runbook || !line.includes('RUNBOOK.md')).join('\n');
}

export function setupProject({ cwd, packageRoot }) {
  const wanted = block(packageRoot);
  const file = join(cwd, existsSync(join(cwd, 'CLAUDE.md')) ? 'CLAUDE.md' : 'AGENTS.md');
  const old = existsSync(file) ? readFileSync(file, 'utf8') : null;
  let text;
  if (old === null) text = `${wanted}\n`;
  else {
    const lines = old.split('\n'), starts = lines.filter(line => line === START).length, ends = lines.filter(line => line === END).length;
    const start = lines.indexOf(START), end = lines.indexOf(END);
    if (starts === 0 && ends === 0) text = `${old}${old.endsWith('\n') ? '' : '\n'}\n${wanted}\n`;
    else if (starts === 1 && ends === 1 && start < end) text = [...lines.slice(0, start), wanted, ...lines.slice(end + 1)].join('\n');
    else throw Error(`${file} needs exactly one ${START} line followed by one ${END} line. Fix the markers, then run pdd setup again.`);
  }
  if (!text.endsWith('\n')) text += '\n';
  if (text === old) return { file, changed: false };
  writeFileSync(file, text);
  return { file, changed: true };
}

// pdd test keeps its local cache in .pdd/ at the Git root; a commit must never carry it.
const IGNORED = new Set(['.pdd', '.pdd/', '/.pdd', '/.pdd/']);
export function ignorePddFolder({ root }) {
  const file = join(root, '.gitignore');
  let old = null;
  try {
    if (!lstatSync(file).isFile()) throw Error(`${file} is not a regular file. Add the line .pdd/ to it by hand.`);
    old = readFileSync(file, 'utf8');
  } catch (error) { if (error.code !== 'ENOENT') throw error; }
  if (old !== null && old.split(/\r?\n/).some(line => IGNORED.has(line.trim()))) return { file, changed: false };
  writeFileSync(file, `${old ?? ''}${old && !old.endsWith('\n') ? '\n' : ''}.pdd/\n`);
  return { file, changed: true };
}
