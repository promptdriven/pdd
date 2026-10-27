// Generated from prompts/cli/skills-install.prompt.md (sha256: e9c462b10ba1529c7a735dcf60c0378776dc175fa306400b2bdc9f615bca8884).
import { createHash } from 'node:crypto';
import { cpSync, lstatSync, mkdirSync, readFileSync, readdirSync, renameSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

export const PDD_SKILL_NAMES = Object.freeze(['pdd-prompting', 'pdd-small-change', 'pdd-bug', 'pdd-feature']);
const SKILL_ROOTS = ['.agents/skills', '.claude/skills'];
const MARKER = '.pdd-skill.json';

const relativeFiles = (dir, prefix = '') => readdirSync(dir, { withFileTypes: true }).flatMap(entry =>
  entry.isDirectory() ? relativeFiles(join(dir, entry.name), `${prefix}${entry.name}/`) : [`${prefix}${entry.name}`]);
function digest(dir) {
  const hash = createHash('sha256');
  for (const file of relativeFiles(dir).sort()) hash.update(`${file}\0`).update(readFileSync(join(dir, file))).update('\0');
  return hash.digest('hex');
}
const versionParts = version => String(version).split('.').slice(0, 3).map(part => parseInt(part, 10) || 0);
function compareVersions(a, b) {
  const [x, y] = [versionParts(a), versionParts(b)];
  for (let i = 0; i < 3; i++) if ((x[i] ?? 0) !== (y[i] ?? 0)) return (x[i] ?? 0) < (y[i] ?? 0) ? -1 : 1;
  return 0;
}
function shouldCopy(dest, version, sum) {
  let info;
  try { info = lstatSync(dest); } catch (error) { if (error.code === 'ENOENT') return true; throw error; }
  if (!info.isDirectory()) return false;
  let text;
  try { text = readFileSync(join(dest, MARKER), 'utf8'); } catch (error) { if (error.code === 'ENOENT') return false; throw error; }
  let marker;
  try { marker = JSON.parse(text); } catch { return true; }
  const order = compareVersions(marker?.version, version);
  return order < 0 || (order === 0 && marker.digest !== sum);
}

function installRoot(parent, skills, version, installed, kept) {
  for (const { name, source, digest: sum } of skills) {
    const dest = join(parent, name);
    if (!shouldCopy(dest, version, sum)) { kept.push(dest); continue; }
    mkdirSync(parent, { recursive: true });
    const staging = join(parent, `.${name}.pdd-install-${process.pid}`);
    try {
      rmSync(staging, { recursive: true, force: true });
      cpSync(source, staging, { recursive: true });
      writeFileSync(join(staging, MARKER), `${JSON.stringify({ package: 'pdd', version, digest: sum })}\n`);
      rmSync(dest, { recursive: true, force: true });
      renameSync(staging, dest);
    } finally { rmSync(staging, { recursive: true, force: true }); }
    installed.push(dest);
  }
}

export function installSkills({ packageRoot, home }) {
  const version = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
  const skills = PDD_SKILL_NAMES.map(name => ({ name, source: join(packageRoot, 'skills', name) }))
    .map(skill => ({ ...skill, digest: digest(skill.source) }));
  const installed = [], kept = [], errors = [];
  // A broken root (for example a file named ~/.agents) must not stop the other agent's copy.
  for (const skillRoot of SKILL_ROOTS) {
    try { installRoot(join(home, skillRoot), skills, version, installed, kept); } catch (error) { errors.push(error); }
  }
  if (errors.length) throw errors[0];
  return { installed, kept };
}
