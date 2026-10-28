// Generated from prompts/cli/skills-install.prompt.md (sha256: b47581febbaa427092bcf680f2c02a30f88bd9613860125a6675e5592fb1c36b).
import { createHash } from 'node:crypto';
import { cpSync, lstatSync, mkdirSync, readFileSync, readdirSync, renameSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { isAbsolute, join } from 'node:path';

export const PDD_SKILL_NAMES = Object.freeze(['pdd-prompting', 'pdd-setup', 'pdd-small-change', 'pdd-bug', 'pdd-feature']);
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
// 'missing', 'update' (a pdd-owned copy that is older or changed) or 'keep'.
function copyState(dest, version, sum) {
  let info;
  try { info = lstatSync(dest); } catch (error) { if (error.code === 'ENOENT') return 'missing'; throw error; }
  if (!info.isDirectory()) return 'keep';
  let text;
  try { text = readFileSync(join(dest, MARKER), 'utf8'); } catch (error) { if (error.code === 'ENOENT') return 'keep'; throw error; }
  let marker;
  try { marker = JSON.parse(text); } catch { return 'update'; }
  const order = compareVersions(marker?.version, version);
  return order < 0 || (order === 0 && marker.digest !== sum) ? 'update' : 'keep';
}

function copySkill(source, parent, name, version, sum) {
  const dest = join(parent, name), staging = join(parent, `.${name}.pdd-install-${process.pid}`);
  mkdirSync(parent, { recursive: true });
  try {
    rmSync(staging, { recursive: true, force: true });
    cpSync(source, staging, { recursive: true });
    writeFileSync(join(staging, MARKER), `${JSON.stringify({ package: 'pdd', version, digest: sum })}\n`);
    rmSync(dest, { recursive: true, force: true });
    renameSync(staging, dest);
  } finally { rmSync(staging, { recursive: true, force: true }); }
  return dest;
}

// How a found skill folder compares with the package: 'older' (its pdd marker has an older version), 'differs' (other
// files, or a marker of the same version with another digest), or null (the same, newer, or pdd cannot read it).
function foundState(dir, version, sum) {
  let text;
  try { text = readFileSync(join(dir, MARKER), 'utf8'); }
  catch {
    // No marker: an npx skills copy or the person's own. Compare the files.
    try { return digest(dir) === sum ? null : 'differs'; } catch { return null; }
  }
  let marker;
  try { marker = JSON.parse(text); } catch { return 'differs'; }
  const order = compareVersions(marker?.version, version);
  return order < 0 ? 'older' : order === 0 && marker.digest !== sum ? 'differs' : null;
}

const hasSkill = (folder, name) => { try { return statSync(join(folder, name, 'SKILL.md')).isFile(); } catch { return false; } };

function setupAgent({ agent, read, root }, skills, version) {
  const result = { agent, root, found: null, stale: null, installed: [], updated: [] };
  try {
    for (const { name, source, digest: sum } of skills)
      if (copyState(join(root, name), version, sum) === 'update') result.updated.push(copySkill(source, root, name, version, sum));
    // A symlinked skill folder (npx skills add) counts as found.
    result.found = read.find(folder => skills.every(({ name }) => hasSkill(folder, name))) ?? null;
    // Found skills that are not this package's: setup never touches them, but says so (0.1.6 tester).
    const states = result.found ? skills.map(({ name, digest: sum }) => foundState(join(result.found, name), version, sum)).filter(Boolean) : [];
    if (states.length) result.stale = states.every(state => state === 'older') ? 'older' : 'differs';
    if (!result.found) for (const { name, source, digest: sum } of skills)
      if (copyState(join(root, name), version, sum) === 'missing') result.installed.push(copySkill(source, root, name, version, sum));
  } catch (error) { result.error = error; }
  return result;
}

export function setupSkills({ packageRoot, cwd, home, claudeConfigDir }) {
  const version = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
  const skills = PDD_SKILL_NAMES.map(name => ({ name, source: join(packageRoot, 'skills', name) }))
    .map(skill => ({ ...skill, digest: digest(skill.source) }));
  // Claude reads <CLAUDE_CONFIG_DIR>/skills instead of ~/.claude/skills when that variable is set.
  const claudeRoot = claudeConfigDir && isAbsolute(claudeConfigDir) ? join(claudeConfigDir, 'skills') : join(home, '.claude/skills');
  const agents = [
    { agent: 'Codex', root: join(home, '.agents/skills'), read: [join(cwd, '.agents/skills'), join(home, '.agents/skills')] },
    { agent: 'Claude', root: claudeRoot, read: [join(cwd, '.claude/skills'), claudeRoot] },
  ];
  return agents.map(agent => setupAgent(agent, skills, version));
}
