// Prompt: prompts/cli/skills-install.prompt.md
import { createHash } from 'node:crypto';
import {
  accessSync,
  constants,
  cpSync,
  existsSync,
  lstatSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  readlinkSync,
  realpathSync,
  renameSync,
  rmSync,
  statSync,
  unlinkSync,
  writeFileSync,
} from 'node:fs';
import { delimiter, dirname, isAbsolute, join, relative, resolve } from 'node:path';
import { resolvePddStateBase } from './state-dir.mjs';

export const PDD_SKILL_NAMES = Object.freeze(['pdd']);
// Skills that the package no longer ships. Setup and sync remove PDD-managed copies and retired agent-root/dangling symlinks in user folders.
export const RETIRED_SKILL_NAMES = Object.freeze([
  'pdd-autopilot',
  'pdd-check',
  'pdd-merge',
  'pdd-setup',
  'pdd-prompting',
  'pdd-small-change',
  'pdd-bug',
  'pdd-feature',
  'pdd-product',
  'pdd-graph',
]);
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

const canonicalPath = folder => { try { return realpathSync(folder); } catch { return resolve(folder); } };
const hasGitDir = dir => { try { return existsSync(join(dir, '.git')); } catch { return false; } };

function isInsideGitCheckout(targetPath, home) {
  const stopAt = home ? canonicalPath(home) : null;
  let cur = resolve(targetPath);
  for (let depth = 0; depth < 64; depth++) {
    const canon = canonicalPath(cur);
    if (stopAt && canon === stopAt) return false;
    if (hasGitDir(canon)) return true;
    const parent = dirname(canon);
    if (parent === canon) break;
    cur = parent;
  }
  return false;
}

function isInsideAnyRoot(targetPath, roots) {
  const canonTarget = canonicalPath(targetPath);
  for (const root of roots) {
    const canonRoot = canonicalPath(root);
    const rel = relative(canonRoot, canonTarget);
    if (rel && !rel.startsWith('..') && !isAbsolute(rel)) return true;
  }
  return false;
}

// The `pdd-skills: VERSION` line in a regular non-symlink SKILL.md frontmatter (LF or CRLF), or null.
function skillVersion(dir) {
  try {
    const skillFile = join(dir, 'SKILL.md');
    if (!lstatSync(skillFile).isFile()) return null;
    const text = readFileSync(skillFile, 'utf8');
    const frontmatter = text.match(/^---\r?\n([\s\S]*?)\r?\n---(?:\r?\n|$)/)?.[1];
    return frontmatter?.match(/^\s*pdd-skills:\s*["']?(\d[\d.]*(?:-[0-9A-Za-z.-]+)?)/m)?.[1] ?? null;
  } catch { return null; }
}

function hasMarkerFile(dir) {
  try { return lstatSync(join(dir, MARKER)).isFile(); }
  catch (error) { if (error.code === 'ENOENT') return false; throw error; }
}

function markerVersion(dir) {
  try {
    if (!lstatSync(join(dir, MARKER)).isFile()) return null;
    const parsed = JSON.parse(readFileSync(join(dir, MARKER), 'utf8'));
    return typeof parsed?.version === 'string' && parsed.version ? parsed.version : null;
  } catch { return null; }
}

// True for a real non-git directory holding `.pdd-skill.json` (any content) OR `pdd-skills: <version>` in SKILL.md frontmatter.
function pddManaged(dest) {
  let info;
  try { info = lstatSync(dest); } catch (error) { if (error.code === 'ENOENT') return false; throw error; }
  if (!info.isDirectory()) return false;
  if (hasGitDir(dest)) return false;
  if (hasMarkerFile(dest)) return true;
  return skillVersion(dest) !== null;
}

// 'missing', 'update' (a PDD-managed copy that is older, differing, or has an invalid marker) or 'keep'.
function copyState(dest, version, sum) {
  let info;
  try { info = lstatSync(dest); } catch (error) { if (error.code === 'ENOENT') return 'missing'; throw error; }
  if (!info.isDirectory()) return 'keep';
  if (hasGitDir(dest)) return 'keep';
  if (hasMarkerFile(dest)) {
    let marker;
    try { marker = JSON.parse(readFileSync(join(dest, MARKER), 'utf8')); } catch { return 'update'; }
    const order = compareVersions(marker?.version, version);
    return order < 0 || (order === 0 && marker.digest !== sum) ? 'update' : 'keep';
  }
  const tagged = skillVersion(dest);
  if (tagged === null) return 'keep';
  const order = compareVersions(tagged, version);
  if (order > 0) return 'keep';
  if (order < 0) return 'update';
  try { return digest(dest) !== sum ? 'update' : 'keep'; } catch { return 'update'; }
}

// Classify a retired skill entry as 'dir' (PDD-managed real directory), 'symlink' (dangling or agent-root PDD symlink), or null.
function retiredEntryKind(dest, { knownAgentRoots = [], projectRoots = null, home = null } = {}) {
  let info;
  try { info = lstatSync(dest); } catch (error) { if (error.code === 'ENOENT') return null; throw error; }
  if (info.isSymbolicLink()) {
    let targetStat;
    try {
      targetStat = statSync(dest);
    } catch (error) {
      if (error.code === 'ENOENT' || error.code === 'ENOTDIR') {
        // Protect dangling developer symlinks whose target path lives inside a git checkout.
        try {
          const lexicalTarget = resolve(dirname(dest), readlinkSync(dest));
          if (isInsideGitCheckout(lexicalTarget, home)) return null;
        } catch { /* Unreadable link target falls through. */ }
        return 'symlink';
      }
      return null;
    }
    let resolvedTarget;
    try { resolvedTarget = realpathSync(dest); } catch { return null; }
    const inProjectDiscovery = Boolean(projectRoots && isInsideAnyRoot(resolvedTarget, projectRoots));
    if (!inProjectDiscovery && isInsideGitCheckout(resolvedTarget, home)) return null;
    if (targetStat.isDirectory() && isInsideAnyRoot(resolvedTarget, knownAgentRoots) && pddManaged(resolvedTarget)) {
      return 'symlink';
    }
    return null;
  }
  if (info.isDirectory()) return pddManaged(dest) ? 'dir' : null;
  return null;
}

function copySkill(source, parent, name, version, sum) {
  const dest = join(parent, name);
  const staging = join(parent, `.${name}.pdd-install-${process.pid}`);
  const backup = join(parent, `.${name}.pdd-backup-${process.pid}`);
  mkdirSync(parent, { recursive: true });
  let movedBackup = false;
  try {
    rmSync(staging, { recursive: true, force: true });
    rmSync(backup, { recursive: true, force: true });
    cpSync(source, staging, { recursive: true });
    writeFileSync(join(staging, MARKER), `${JSON.stringify({ package: 'pdd', version, digest: sum })}\n`);
    if (existsSync(dest)) {
      renameSync(dest, backup);
      movedBackup = true;
    }
    renameSync(staging, dest);
    if (movedBackup) rmSync(backup, { recursive: true, force: true });
  } catch (error) {
    if (movedBackup && !existsSync(dest) && existsSync(backup)) {
      try { renameSync(backup, dest); } catch { /* Best-effort rollback */ }
    }
    throw error;
  } finally {
    rmSync(staging, { recursive: true, force: true });
  }
  return dest;
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

function resolveClaudeBase({ home, claudeConfigDir }) {
  return claudeConfigDir && isAbsolute(claudeConfigDir) ? claudeConfigDir : join(home, '.claude');
}

function userAgentSkillRoots({ home, claudeConfigDir, codexHome } = {}) {
  const roots = [];
  if (home) {
    roots.push(
      join(home, '.agents/skills'),
      join(home, '.codex/skills'),
      join(home, '.gemini/config/skills'),
      join(home, '.gemini/skills'),
    );
  }
  if (codexHome && isAbsolute(codexHome)) roots.push(join(codexHome, 'skills'));
  if (home || (claudeConfigDir && isAbsolute(claudeConfigDir))) {
    roots.push(join(resolveClaudeBase({ home: home || '', claudeConfigDir }), 'skills'));
  }
  return [...new Set(roots.map(canonicalPath))];
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

function removeOwnedRetiredSkills(root, ctx) {
  const removed = [];
  for (const name of RETIRED_SKILL_NAMES) {
    const dest = join(root, name);
    const kind = retiredEntryKind(dest, ctx);
    if (kind === 'symlink') {
      unlinkSync(dest);
      removed.push(dest);
    } else if (kind === 'dir') {
      rmSync(dest, { recursive: true, force: true });
      removed.push(dest);
    }
  }
  return removed;
}

function retiredSkillInfo(dest, ctx) {
  const kind = retiredEntryKind(dest, ctx);
  if (!kind) return null;
  if (kind === 'symlink') {
    let ver = null;
    try {
      const resolved = realpathSync(dest);
      ver = markerVersion(resolved) ?? skillVersion(resolved);
    } catch { /* Dangling symlink */ }
    return { kind: 'symlink', version: ver };
  }
  return { kind: 'dir', version: markerVersion(dest) ?? skillVersion(dest) };
}

function findRetiredIn(folder, ctx) {
  const retiredSkills = [];
  for (const name of RETIRED_SKILL_NAMES) {
    try {
      const info = retiredSkillInfo(join(folder, name), ctx);
      if (info) retiredSkills.push({ name, ...info });
    } catch { /* Unreadable entry ignored in read-only discovery. */ }
  }
  return retiredSkills;
}

function setupAgent({ agent, read, root, pluginManaged = null }, skills, version, ctx) {
  if (pluginManaged) {
    const result = { agent, root, found: pluginManaged, pluginManaged: true, stale: null, staleSkills: [], installed: [], updated: [], removed: [] };
    try {
      result.removed.push(...removeOwnedRetiredSkills(root, ctx));
    } catch (error) { result.error = error; }
    return result;
  }
  const result = { agent, root, found: null, stale: null, staleSkills: [], installed: [], updated: [], removed: [] };
  try {
    for (const { name, source, digest: sum } of skills)
      if (copyState(join(root, name), version, sum) === 'update') result.updated.push(copySkill(source, root, name, version, sum));
    Object.assign(result, findIn(read, skills, version));
    if (!result.found) for (const { name, source, digest: sum } of skills)
      if (copyState(join(root, name), version, sum) === 'missing') result.installed.push(copySkill(source, root, name, version, sum));
    result.removed.push(...removeOwnedRetiredSkills(root, ctx));
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

function hasOwnedSkill(root, ctx) {
  try { if (!statSync(root).isDirectory()) return false; } catch { return false; }
  for (const name of PDD_SKILL_NAMES) {
    try { if (pddManaged(join(root, name))) return true; } catch { /* Unreadable entry is not managed. */ }
  }
  for (const name of RETIRED_SKILL_NAMES) {
    try { if (retiredEntryKind(join(root, name), ctx) !== null) return true; } catch { /* Unreadable entry is not managed. */ }
  }
  return false;
}

function hasOwnedRetiredSkill(root, ctx) {
  try { if (!statSync(root).isDirectory()) return false; } catch { return false; }
  for (const name of RETIRED_SKILL_NAMES) {
    try { if (retiredEntryKind(join(root, name), ctx) !== null) return true; } catch { /* Unreadable entry is not managed. */ }
  }
  return false;
}

export function setupSkills(options) {
  const { packageRoot, cwd = process.cwd(), home, claudeConfigDir, codexHome, skillsDir, env = process.env } = options;
  const { version, skills } = loadBundledSkills(packageRoot);
  const ctx = { knownAgentRoots: userAgentSkillRoots({ home, claudeConfigDir, codexHome }), home };

  if (typeof skillsDir === 'string' && skillsDir.trim()) {
    const customRoot = resolve(cwd, skillsDir.trim());
    return [setupAgent({ agent: 'Custom', root: customRoot, read: [customRoot] }, skills, version, ctx)];
  }

  const claudeRoot = join(resolveClaudeBase({ home, claudeConfigDir }), 'skills');
  const pluginManaged = hasClaudePluginInstall({ home, claudeConfigDir });
  const agyRoot = join(home, '.gemini/config/skills');
  const agents = [
    { agent: 'Codex', root: join(home, '.agents/skills'), read: [join(home, '.agents/skills')] },
    { agent: 'Claude', root: claudeRoot, read: [claudeRoot], pluginManaged },
    ...(hasAntigravityInstall({ home, env }) || hasOwnedSkill(agyRoot, ctx)
      ? [{ agent: 'Antigravity', root: agyRoot, read: [agyRoot] }]
      : []),
  ];
  const results = agents.map(agent => setupAgent(agent, skills, version, ctx));
  const seen = new Set(results.map(result => canonicalPath(result.root)));
  for (const root of secondaryCodexRoots(options)) {
    const key = canonicalPath(root);
    if (seen.has(key)) continue;
    seen.add(key);
    if (hasOwnedSkill(root, ctx)) results.push(setupAgent({ agent: 'Codex', root, read: [root] }, skills, version, ctx));
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
  const resolvedStateRoot = stateRoot || resolvePddStateBase(env ? { ...(home ? { HOME: home } : {}), ...env } : { HOME: home });
  const syncFile = join(resolvedStateRoot, 'skills-sync.json');
  if (!force) {
    try {
      if (JSON.parse(readFileSync(syncFile, 'utf8'))?.version === version) return { updated: [] };
    } catch { /* Missing or unreadable sync state falls through to folder inspection. */ }
  }
  const ctx = { knownAgentRoots: userAgentSkillRoots({ home, claudeConfigDir, codexHome }), home };
  const claudeRoot = join(resolveClaudeBase({ home, claudeConfigDir }), 'skills');
  const claudePluginManaged = Boolean(hasClaudePluginInstall({ home, claudeConfigDir }));
  const candidates = [
    join(home, '.agents/skills'),
    ...secondaryCodexRoots({ home, codexHome }),
    ...(claudePluginManaged ? [] : [claudeRoot]),
    join(home, '.gemini/config/skills'),
  ];
  const seen = new Set();
  const inspectedRoots = [];
  const ownedRoots = [];
  for (const root of candidates) {
    const key = canonicalPath(root);
    if (seen.has(key)) continue;
    seen.add(key);
    inspectedRoots.push(root);
    if (hasOwnedSkill(root, ctx)) ownedRoots.push(root);
  }
  const retiredOnlyRoots = [];
  if (claudePluginManaged) {
    const claudeKey = canonicalPath(claudeRoot);
    if (!seen.has(claudeKey)) {
      seen.add(claudeKey);
      inspectedRoots.push(claudeRoot);
      if (hasOwnedRetiredSkill(claudeRoot, ctx)) retiredOnlyRoots.push(claudeRoot);
    }
  }
  if (!ownedRoots.length && !retiredOnlyRoots.length) {
    const anyRetiredRemaining = inspectedRoots.some(root => findRetiredIn(root, ctx).length > 0);
    if (!anyRetiredRemaining) writeSyncState(resolvedStateRoot, syncFile, version);
    return { updated: [] };
  }
  let skills = [];
  if (ownedRoots.length) {
    try {
      skills = PDD_SKILL_NAMES.map(name => ({ name, source: join(packageRoot, 'skills', name) }))
        .map(skill => ({ ...skill, digest: digest(skill.source) }));
    } catch (error) {
      onError?.(packageRoot, error);
      return { updated: [] };
    }
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
      if (removeOwnedRetiredSkills(root, ctx).length > 0) changed = true;
      if (changed) updated.push(root);
    } catch (error) {
      hadError = true;
      onError?.(root, error);
    }
  }
  for (const root of retiredOnlyRoots) {
    try {
      if (removeOwnedRetiredSkills(root, ctx).length > 0) updated.push(root);
    } catch (error) {
      hadError = true;
      onError?.(root, error);
    }
  }
  const anyRetiredRemaining = inspectedRoots.some(root => findRetiredIn(root, ctx).length > 0);
  if (!hadError && !anyRetiredRemaining) writeSyncState(resolvedStateRoot, syncFile, version);
  return { updated };
}

// Read-only discovery, stale check, and stranded retired-skill check across project and user folders (for `pdd --version` and `pdd upgrade`).
export function findSkills(options) {
  const { packageRoot, cwd = process.cwd(), home, claudeConfigDir, codexHome } = options;
  const { version, skills } = loadBundledSkills(packageRoot);
  const claudeRoot = join(resolveClaudeBase({ home, claudeConfigDir }), 'skills');
  const userRoots = userAgentSkillRoots({ home, claudeConfigDir, codexHome });
  const userRootSet = new Set(userRoots);
  const sameAsHome = Boolean(home && canonicalPath(cwd) === canonicalPath(home));
  const rawProjectList = sameAsHome ? [] : [
    join(cwd, '.agents/skills'),
    join(cwd, '.codex/skills'),
    join(cwd, '.claude/skills'),
  ].filter(folder => !userRootSet.has(canonicalPath(folder)));
  const projectRoots = new Set(rawProjectList.map(canonicalPath));
  const ctxFor = scope => ({
    knownAgentRoots: scope === 'project' ? [...userRoots, ...projectRoots] : userRoots,
    projectRoots: scope === 'project' ? [...projectRoots] : null,
    home,
  });
  const scopeOf = folder => {
    if (!folder) return null;
    const key = canonicalPath(folder);
    if (userRootSet.has(key)) return 'user';
    return projectRoots.has(key) ? 'project' : 'user';
  };
  const agents = [
    { agent: 'Codex', read: [...(sameAsHome ? [] : [join(cwd, '.agents/skills')]), join(home, '.agents/skills')] },
    { agent: 'Claude', read: [...(sameAsHome ? [] : [join(cwd, '.claude/skills')]), claudeRoot] },
    { agent: 'Antigravity', read: [join(home, '.gemini/config/skills')] },
  ];
  const results = agents.map(({ agent, read }) => {
    const info = findIn(read, skills, version);
    const scope = info.found ? scopeOf(info.found) : null;
    const retiredSkills = info.found ? findRetiredIn(info.found, ctxFor(scope)) : [];
    return { agent, scope, root: info.found, ...info, retiredSkills };
  });
  const seen = new Set(results.map(result => result.found).filter(Boolean).map(canonicalPath));
  const candidates = [
    ...(sameAsHome ? [] : [
      [join(cwd, '.agents/skills'), 'Codex', 'project'],
      [join(cwd, '.codex/skills'), 'Codex', 'project'],
    ]),
    [join(home, '.agents/skills'), 'Codex', 'user'],
    ...(codexHome && isAbsolute(codexHome) ? [[join(codexHome, 'skills'), 'Codex', 'user']] : []),
    [join(home, '.codex/skills'), 'Codex', 'user'],
    ...(sameAsHome ? [] : [[join(cwd, '.claude/skills'), 'Claude', 'project']]),
    [claudeRoot, 'Claude', 'user'],
    [join(home, '.gemini/config/skills'), 'Antigravity', 'user'],
  ];
  for (const [folder, agent, scope] of candidates) {
    const key = canonicalPath(folder);
    if (seen.has(key)) continue;
    seen.add(key);
    const effectiveScope = userRootSet.has(key) ? 'user' : scope;
    const staleSkills = skills.flatMap(({ name, digest: sum }) => {
      if (!hasSkill(folder, name)) return [];
      const status = foundState(join(folder, name), version, sum);
      return status ? [{ name, ...status }] : [];
    });
    const retiredSkills = findRetiredIn(folder, ctxFor(effectiveScope));
    const hasOlder = staleSkills.some(({ state }) => state === 'older');
    if (hasOlder || retiredSkills.length > 0) {
      const hasAnyCurrent = skills.some(({ name }) => hasSkill(folder, name));
      results.push({
        agent,
        scope: effectiveScope,
        root: folder,
        found: hasAnyCurrent ? folder : null,
        stale: !staleSkills.length ? null : staleSkills.every(({ state }) => state === 'older') ? 'older' : 'differs',
        staleSkills,
        retiredSkills,
      });
    }
  }
  return results;
}
