// Generated from prompts/cli/project-setup.prompt.md (sha256: 4ad1ae59ff57c4e131a5f692fdf5bcb2280b513ca1115b8eb80e905c03d084ac).
import { appendFileSync, existsSync, lstatSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

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
// Bytes, not text: a line check needs ASCII only, and the append keeps every old byte (also non-UTF-8 ones).
const IGNORED = new Set(['.pdd', '.pdd/', '/.pdd', '/.pdd/']);
// A "!" line for .pdd or a path in it, such as !.pdd/config.json: a .pdd/ line after it would override it.
const NEGATION = /^!\/?(\*\*\/)?\.pdd($|[/*?[])/;
export function ignorePddFolder({ root }) {
  const file = join(root, '.gitignore');
  let old = null;
  try {
    if (!lstatSync(file).isFile()) throw Error(`${file} is not a regular file. Add the line .pdd/ to it by hand.`);
    old = readFileSync(file);
  } catch (error) { if (error.code !== 'ENOENT') throw error; }
  if (old === null) { writeFileSync(file, '.pdd/\n', { flag: 'wx' }); return { file, changed: true, negated: false }; }
  // Git drops trailing spaces and a CR, never leading spaces; the last matching line wins.
  const lines = old.toString('latin1').split('\n').map(line => line.replace(/[ \r]+$/, ''));
  const last = lines.findLast(line => IGNORED.has(line) || line.startsWith('!') && IGNORED.has(line.slice(1)));
  if (last !== undefined) return { file, changed: false, negated: last.startsWith('!') };
  if (lines.some(line => NEGATION.test(line))) return { file, changed: false, negated: true };
  const newline = old.includes('\r\n') ? '\r\n' : '\n';
  appendFileSync(file, `${old.length && old.at(-1) !== 0x0a ? newline : ''}.pdd/${newline}`);
  return { file, changed: true, negated: false };
}

export function checkProjectReady({ cwd, packageRoot }) {
  try {
    const file = join(cwd, existsSync(join(cwd, 'CLAUDE.md')) ? 'CLAUDE.md' : 'AGENTS.md');
    const lines = readFileSync(file, 'utf8').split('\n');
    const start = lines.indexOf(START), end = lines.indexOf(END);
    if (start < 0 || end <= start || lines.filter(x => x === START).length !== 1 || lines.filter(x => x === END).length !== 1 || lines.slice(start, end + 1).join('\n') !== block(packageRoot)) return false;
    const git = spawnSync('git', ['rev-parse', '--show-toplevel'], { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
    if (git.status !== 0) return true;
    const ignore = join(git.stdout.trim(), '.gitignore');
    if (!lstatSync(ignore).isFile()) return false;
    const rules = readFileSync(ignore).toString('latin1').split('\n').map(x => x.replace(/[ \r]+$/, ''));
    return rules.some(x => IGNORED.has(x) || x.startsWith('!') && IGNORED.has(x.slice(1)) || NEGATION.test(x));
  } catch { return false; }
}
