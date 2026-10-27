// Generated from prompts/cli/project-setup.prompt.md (sha256: 858668c63ebd6e8ed987bc1cc12b513f887538119c421e11ca5ccbb5023c6c06).
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
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
