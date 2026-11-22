// Prompt: prompts/cli/skills-install.prompt.md
import { createHash } from 'node:crypto';
import { accessSync, constants, cpSync, existsSync, lstatSync, mkdirSync, readFileSync, readdirSync, realpathSync, renameSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { delimiter, isAbsolute, join, relative, resolve } from 'node:path';
import { resolvePddStateBase } from './state-dir.mjs';

export const PDD_SKILL_NAMES = Object.freeze([
  'pdd',
  'pdd-prompting',
  'pdd-small-change',
  'pdd-bug',
  'pdd-feature',
  'pdd-product',
  'pdd-graph',
]);
// Skills that the package no longer ships. Setup and sync remove only their pdd-owned copies in user folders.
export const RETIRED_SKILL_NAMES = Object.freeze(['pdd-autopilot', 'pdd-check', 'pdd-merge', 'pdd-setup']);
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
  try {
    if (!lstatSync(join(dest, MARKER)).isFile()) return 'keep';
    text = readFileSync(join(dest, MARKER), 'utf8');
  } catch (error) { if (error.code === 'ENOENT') return 'keep'; throw error; }
  let marker;
  try { marker = JSON.parse(text); } catch { return 'update'; }
  const order = compareVersions(marker?.version, version);
  return order < 0 || (order === 0 && marker.digest !== sum) ? 'update' : 'keep';
}

// True for a real folder (not a symlink or a file) that holds the pdd marker file, with any content.
function pddOwned(dest) {
  let info;
  try { info = lstatSync(dest); } catch (error) { if (error.code === 'ENOENT') return false; throw error; }
  if (!info.isDirectory()) return false;
  try { return lstatSync(join(dest, MARKER)).isFile(); } catch (error) { if (error.code === 'ENOENT') return false; throw error; }
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

// The `pdd-skills: VERSION` line in SKILL.md frontmatter, or null.
function skillVersion(dir) {
  try { return readFileSync(join(dir, 'SKILL.md'), 'utf8').match(/^---\n([\s\S]*?)\n---/)?.[1].match(/^\s*pdd-skills:\s*["']?(\d[\d.]*)/m)?.[1] ?? null; }
  catch { return null; }
}

function foundState(dir, version, sum) {
  let text;
  try { text = readFileSync(join(dir, MARKER), 'utf8'); }
  catch {
    try {
      if (digest(dir) === sum) return null;
      const line = skillVersion(dir), order = line ? compareVersions(line, version) : -1;
      return order <= 0 ? { state: order < 0 ? 'older' : 'differs', version: line } : null;
    } catch { return null; }
  }
  let marker;
  try { marker = JSON.parse(text); } catch { return { state: 'differs', version: null }; }
  const order = compareVersions(marker?.version, version);
  const state = order < 0 ? 'older' : order === 0 && marker.digest !== sum ? 'differs' : null;
  return state ? { state, version: typeof marker?.version === 'string' ? marker.version : null } : null;
}

const hasSkill = (folder, name) => { try { return statSync(join(folder, name, 'SKILL.md')).isFile(); } catch { return false; } };
const canonicalPath = folder => { try { return realpathSync(folder); } catch { return folder; } };

function resolveClaudeBase({ home, claudeConfigDir }) {
  return claudeConfigDir && isAbsolute(claudeConfigDir) ? claudeConfigDir : join(home, '.claude');
}

const PDD_PLUGIN_KEY = /^(?:pdd(?:@|$)|promptdriven\/pdd(?:@|$))/i;

function executableOnPath(name, env) {
  return (env?.PATH ?? '').split(delimiter).filter(Boolean).some(folder => {
    try {
      const full = join(folder, name);
      accessSync(full, constants.X_OK);
      const st = lstatSync(full);
      return st.isFile() || st.isSymbolicLink();
    } catch { return false; }
  });
}

function hasAntigravityInstall({ home, env }) {
  if (!home) return false;
  return existsSync(join(home, '.gemini/antigravity-cli'))
    || existsSync(join(home, '.gemini/config/mcp_config.json'))
    || executableOnPath('agy', env);
}

// Detect a Claude Code plugin-managed PDD install so `pdd setup` avoids duplicate `/pdd` skills.
export function hasClaudePluginInstall({ home, claudeConfigDir } = {}) {
  if (!home && !(claudeConfigDir && isAbsolute(claudeConfigDir))) return null;
  const pluginsFile = join(resolveClaudeBase({ home: home || '', claudeConfigDir }), 'plugins', 'installed_plugins.json');
  let parsed;
  try { parsed = JSON.parse(readFileSync(pluginsFile, 'utf8')); } catch { return null; }
  if (!parsed || typeof parsed !== 'object') return null;
  const entries = parsed.plugins && typeof parsed.plugins === 'object' ? parsed.plugins : parsed;
  const matchKey = key => PDD_PLUGIN_KEY.test(String(key ?? ''));
  if (Array.isArray(entries)) {
    for (const item of entries) {
      const id = item?.name ?? item?.id ?? item?.plugin ?? item?.repository ?? '';
      if (matchKey(id)) return item?.installPath ?? pluginsFile;
    }
    return null;
  }
  for (const [key, value] of Object.entries(entries)) {
    if (!matchKey(key)) continue;
    if (Array.isArray(value)) {
      if (value.length > 0) return value[0]?.installPath ?? pluginsFile;
    } else if (value && typeof value === 'object') {
      return value.installPath ?? pluginsFile;
    } else if (value) {
      return pluginsFile;
    }
  }
  return null;
}

function findIn(read, skills, version) {
  const found = read.find(folder => skills.every(({ name }) => hasSkill(folder, name))) ?? null;
  const staleSkills = found ? skills.flatMap(({ name, digest: sum }) => {
    const status = foundState(join(found, name), version, sum);
    return status ? [{ name, ...status }] : [];
  }) : [];
  return { found, stale: !staleSkills.length ? null : staleSkills.every(({ state }) => state === 'older') ? 'older' : 'differs', staleSkills };
}

function setupAgent({ agent, read, root, pluginManaged = null }, skills, version) {
  if (pluginManaged) {
    return { agent, root, found: pluginManaged, pluginManaged: true, stale: null, staleSkills: [], installed: [], updated: [], removed: [] };
  }
  const result = { agent, root, found: null, stale: null, staleSkills: [], installed: [], updated: [], removed: [] };
  try {
    for (const { name, source, digest: sum } of skills)
      if (copyState(join(root, name), version, sum) === 'update') result.updated.push(copySkill(source, root, name, version, sum));
    Object.assign(result, findIn(read, skills, version));
    if (!result.found) for (const { name, source, digest: sum } of skills)
      if (copyState(join(root, name), version, sum) === 'missing') result.installed.push(copySkill(source, root, name, version, sum));
    for (const name of RETIRED_SKILL_NAMES) {
      const dest = join(root, name);
      if (pddOwned(dest)) { rmSync(dest, { recursive: true, force: true }); result.removed.push(dest); }
    }
  } catch (error) { result.error = error; }
  return result;
}

function loadBundledSkills(packageRoot) {
  const version = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
  const skills = PDD_SKILL_NAMES.map(name => ({ name, source: join(packageRoot, 'skills', name) }))
    .map(skill => ({ ...skill, digest: digest(skill.source) }));
  return { version, skills };
}

function secondaryCodexRoots({ home, codexHome }) {
  if (!home) return [];
  return [
    join(home, '.codex/skills'),
    ...(codexHome && isAbsolute(codexHome) ? [join(codexHome, 'skills')] : []),
  ];
}

function hasOwnedSkill(root) {
  try { if (!statSync(root).isDirectory()) return false; } catch { return false; }
  for (const name of [...PDD_SKILL_NAMES, ...RETIRED_SKILL_NAMES]) {
    try { if (pddOwned(join(root, name))) return true; } catch { /* Unreadable entry is not owned. */ }
  }
  return false;
}

export function setupSkills(options) {
  const { packageRoot, cwd = process.cwd(), home, claudeConfigDir, skillsDir, env = process.env } = options;
  const { version, skills } = loadBundledSkills(packageRoot);

  if (typeof skillsDir === 'string' && skillsDir.trim()) {
    const customRoot = resolve(cwd, skillsDir.trim());
    return [setupAgent({ agent: 'Custom', root: customRoot, read: [customRoot] }, skills, version)];
  }

  const claudeRoot = join(resolveClaudeBase({ home, claudeConfigDir }), 'skills');
  const pluginManaged = hasClaudePluginInstall({ home, claudeConfigDir });
  const agyRoot = join(home, '.gemini/config/skills');
  const agents = [
    { agent: 'Codex', root: join(home, '.agents/skills'), read: [join(home, '.agents/skills')] },
    { agent: 'Claude', root: claudeRoot, read: [claudeRoot], pluginManaged },
    ...(hasAntigravityInstall({ home, env }) || hasOwnedSkill(agyRoot)
      ? [{ agent: 'Antigravity', root: agyRoot, read: [agyRoot] }]
      : []),
  ];
  const results = agents.map(agent => setupAgent(agent, skills, version));
  const seen = new Set(results.map(result => canonicalPath(result.root)));
  for (const root of secondaryCodexRoots(options)) {
    const key = canonicalPath(root);
    if (seen.has(key)) continue;
    seen.add(key);
    if (hasOwnedSkill(root)) results.push(setupAgent({ agent: 'Codex', root, read: [root] }, skills, version));
  }
  return results;
}

function writeSyncState(resolvedStateRoot, syncFile, version) {
  try {
    mkdirSync(resolvedStateRoot, { recursive: true, mode: 0o700 });
    const tmp = `${syncFile}.${process.pid}.${Date.now()}.tmp`;
    writeFileSync(tmp, `${JSON.stringify({ version })}\n`, { mode: 0o600 });
    renameSync(tmp, syncFile);
  } catch { /* Read-only state folders never disrupt CLI execution. */ }
}

export function syncOwnedUserSkills({ packageRoot, home, claudeConfigDir, codexHome, stateRoot, env, force = false, onError } = {}) {
  if (!home || !packageRoot) return { updated: [] };
  let version;
  try {
    version = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8'))?.version;
    if (typeof version !== 'string' || !version) return { updated: [] };
  } catch { return { updated: [] }; }
  const resolvedStateRoot = stateRoot || resolvePddStateBase(env ?? { HOME: home });
  const syncFile = join(resolvedStateRoot, 'skills-sync.json');
  if (!force) {
    try {
      if (JSON.parse(readFileSync(syncFile, 'utf8'))?.version === version) return { updated: [] };
    } catch { /* Missing or unreadable sync state falls through to folder inspection. */ }
  }
  const claudeRoot = join(resolveClaudeBase({ home, claudeConfigDir }), 'skills');
  const claudePluginManaged = Boolean(hasClaudePluginInstall({ home, claudeConfigDir }));
  const candidates = [
    join(home, '.agents/skills'),
    ...secondaryCodexRoots({ home, codexHome }),
    ...(claudePluginManaged ? [] : [claudeRoot]),
    join(home, '.gemini/config/skills'),
  ];
  const seen = new Set();
  const ownedRoots = [];
  for (const root of candidates) {
    const key = canonicalPath(root);
    if (seen.has(key)) continue;
    seen.add(key);
    if (hasOwnedSkill(root)) ownedRoots.push(root);
  }
  if (!ownedRoots.length) {
    // Record sync state for this version so subsequent commands do not rescan all skill roots indefinitely.
    writeSyncState(resolvedStateRoot, syncFile, version);
    return { updated: [] };
  }
  let skills;
  try {
    skills = PDD_SKILL_NAMES.map(name => ({ name, source: join(packageRoot, 'skills', name) }))
      .map(skill => ({ ...skill, digest: digest(skill.source) }));
  } catch (error) {
    onError?.(packageRoot, error);
    return { updated: [] };
  }
  const updated = [];
  let hadError = false;
  for (const root of ownedRoots) {
    let changed = false;
    try {
      for (const { name, source, digest: sum } of skills) {
        const state = copyState(join(root, name), version, sum);
        if (state === 'update' || state === 'missing') {
          copySkill(source, root, name, version, sum);
          changed = true;
        }
      }
      for (const name of RETIRED_SKILL_NAMES) {
        const dest = join(root, name);
        if (pddOwned(dest)) {
          rmSync(dest, { recursive: true, force: true });
          changed = true;
        }
      }
      if (changed) updated.push(root);
    } catch (error) {
      hadError = true;
      onError?.(root, error);
    }
  }
  if (!hadError) writeSyncState(resolvedStateRoot, syncFile, version);
  return { updated };
}

// Read-only discovery and stale check across project and user folders (for `pdd --version` and `pdd upgrade`).
export function findSkills(options) {
  const { packageRoot, cwd = process.cwd(), home, claudeConfigDir, codexHome } = options;
  const { version, skills } = loadBundledSkills(packageRoot);
  const claudeRoot = join(resolveClaudeBase({ home, claudeConfigDir }), 'skills');
  const projectRoots = new Set([
    canonicalPath(join(cwd, '.agents/skills')),
    canonicalPath(join(cwd, '.codex/skills')),
    canonicalPath(join(cwd, '.claude/skills')),
  ]);
  const scopeOf = folder => (folder && projectRoots.has(canonicalPath(folder)) ? 'project' : 'user');
  const agents = [
    { agent: 'Codex', read: [join(cwd, '.agents/skills'), join(home, '.agents/skills')] },
    { agent: 'Claude', read: [join(cwd, '.claude/skills'), claudeRoot] },
    { agent: 'Antigravity', read: [join(home, '.gemini/config/skills')] },
  ];
  const results = agents.map(({ agent, read }) => {
    const info = findIn(read, skills, version);
    return { agent, scope: info.found ? scopeOf(info.found) : null, ...info };
  });
  const seen = new Set(results.map(result => result.found).filter(Boolean).map(canonicalPath));
  const candidates = [
    [join(cwd, '.agents/skills'), 'Codex', 'project'],
    [join(cwd, '.codex/skills'), 'Codex', 'project'],
    [join(home, '.agents/skills'), 'Codex', 'user'],
    ...(codexHome && isAbsolute(codexHome) ? [[join(codexHome, 'skills'), 'Codex', 'user']] : []),
    [join(home, '.codex/skills'), 'Codex', 'user'],
    [join(cwd, '.claude/skills'), 'Claude', 'project'],
    [claudeRoot, 'Claude', 'user'],
    [join(home, '.gemini/config/skills'), 'Antigravity', 'user'],
  ];
  for (const [folder, agent, scope] of candidates) {
    const key = canonicalPath(folder);
    if (seen.has(key)) continue;
    seen.add(key);
    const staleSkills = skills.flatMap(({ name, digest: sum }) => {
      if (!hasSkill(folder, name)) return [];
      const status = foundState(join(folder, name), version, sum);
      return status ? [{ name, ...status }] : [];
    });
    if (staleSkills.some(({ state }) => state === 'older')) {
      results.push({
        agent,
        scope,
        found: folder,
        stale: staleSkills.every(({ state }) => state === 'older') ? 'older' : 'differs',
        staleSkills,
      });
    }
  }
  return results;
}
