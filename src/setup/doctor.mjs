// Prompt: prompts/cli/doctor.prompt.md

import { spawnSync as nativeSpawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { homedir as nativeHomedir } from 'node:os';
import { delimiter, dirname, isAbsolute, join, resolve } from 'node:path';
import { diagnoseHostInstalls, resolveCanonicalPddTarget, shortenHomePath } from '../path-diagnostic.mjs';
import { quoteShellArg } from '../shared/install-kind.mjs';
import { PACKAGE_ROOT } from '../shared/package-root.mjs';
import { PDD_SKILL_NAMES, RETIRED_SKILL_NAMES } from '../shared/skills-install.mjs';
import { parse as parseToml } from '../shared/toml/parse.js';

const MIN_NODE_VERSION = '22.16.0';
const DEFAULT_TIMEOUT_MS = 1500;
const MAX_CONFIG_BYTES = 2 * 1024 * 1024;
const SKILL_MARKER = '.pdd-skill.json';
const PDD_PLUGIN_KEY = /^(?:pdd(?:@|$)|promptdriven\/pdd(?:@|$))/i;

const isPlainObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const normPath = (value, platform = process.platform) => {
  const normalized = String(value ?? '').replace(/\\/g, '/').replace(/\/+$/, '');
  return platform === 'win32' ? normalized.toLowerCase() : normalized;
};
const cleanText = text => String(text ?? '').replace(/\x1b\[[0-?]*[ -/]*[@-~]/g, '').replace(/[\x00-\x1f\x7f]/g, ' ').replace(/\s+/g, ' ').trim();

function safeQuotePath(targetPath) {
  const str = String(targetPath ?? '');
  if (!/[\x00-\x1f\x7f]/.test(str)) return quoteShellArg(str);
  let out = "$'";
  for (let i = 0; i < str.length; i++) {
    const ch = str[i];
    const code = str.charCodeAt(i);
    if (ch === '\\') out += '\\\\';
    else if (ch === "'") out += "\\'";
    else if (ch === '\n') out += '\\n';
    else if (ch === '\r') out += '\\r';
    else if (ch === '\t') out += '\\t';
    else if (code < 0x20 || code === 0x7f) out += `\\x${code.toString(16).padStart(2, '0')}`;
    else out += ch;
  }
  return `${out}'`;
}

function resolveSafeHome(explicitHome, env, homedirFn = nativeHomedir, platform = process.platform) {
  const isValidAbs = val => {
    if (typeof val !== 'string') return false;
    const trimmed = val.trim();
    if (!trimmed) return false;
    return platform === 'win32' ? /^[A-Za-z]:[\\/]/.test(trimmed) || isAbsolute(trimmed) : isAbsolute(trimmed);
  };
  if (isValidAbs(explicitHome)) return explicitHome.trim();
  if (isValidAbs(env?.HOME)) return env.HOME.trim();
  if (platform === 'win32' && isValidAbs(env?.USERPROFILE)) return env.USERPROFILE.trim();
  try {
    const fallback = homedirFn();
    return isValidAbs(fallback) ? fallback.trim() : '';
  } catch {
    return '';
  }
}

function parseSemver(version) {
  const match = /^v?(\d+)\.(\d+)\.(\d+)/.exec(String(version ?? '').trim());
  if (!match) return null;
  return [Number(match[1]), Number(match[2]), Number(match[3])];
}

function compareSemver(a, b) {
  const pa = parseSemver(a);
  const pb = parseSemver(b);
  if (!pa || !pb) return null;
  for (let i = 0; i < 3; i++) {
    if (pa[i] !== pb[i]) return pa[i] < pb[i] ? -1 : 1;
  }
  return 0;
}

function safeRealpath(target, fs) {
  try { return fs.realpathSync(target); } catch { return target; }
}

function safeExists(target, fs) {
  try { return fs.existsSync(target); } catch { return false; }
}

function executableOnPath(name, env, fs, platform) {
  const raw = env?.PATH ?? (platform === 'win32' ? env?.Path : undefined);
  if (typeof raw !== 'string' || !raw) return false;
  const sep = platform === 'win32' ? ';' : delimiter;
  const names = platform === 'win32' ? [`${name}.cmd`, `${name}.exe`, name] : [name];
  return raw.split(sep).filter(Boolean).some(rawFolder => {
    const folder = platform === 'win32' ? rawFolder.trim().replace(/^"(.*)"$/, '$1') : rawFolder;
    if (!folder) return false;
    return names.some(candidate => {
      try {
        const full = join(folder, candidate);
        fs.accessSync(full, fs.constants?.X_OK ?? nativeFs.constants.X_OK);
        return fs.statSync(full).isFile();
      } catch { return false; }
    });
  });
}

function readJsonBounded(file, fs) {
  try {
    const st = fs.statSync(file);
    if (!st.isFile() || st.size > MAX_CONFIG_BYTES) return null;
    const parsed = JSON.parse(fs.readFileSync(file, 'utf8'));
    return parsed && typeof parsed === 'object' ? parsed : null;
  } catch { return null; }
}

function relativeFiles(dir, fs, prefix = '') {
  const out = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const name = typeof entry === 'string' ? entry : entry.name;
    const full = join(dir, name);
    const isDir = typeof entry === 'string' ? fs.statSync(full).isDirectory() : entry.isDirectory();
    if (isDir) out.push(...relativeFiles(full, fs, `${prefix}${name}/`));
    else out.push(`${prefix}${name}`);
  }
  return out;
}

function digestDir(dir, fs) {
  const hash = createHash('sha256');
  for (const file of relativeFiles(dir, fs).sort()) {
    hash.update(`${file}\0`).update(fs.readFileSync(join(dir, file))).update('\0');
  }
  return hash.digest('hex');
}

function readSkillFrontmatterVersion(dir, fs) {
  try {
    const text = fs.readFileSync(join(dir, 'SKILL.md'), 'utf8');
    return text.match(/^---\r?\n([\s\S]*?)\r?\n---/)?.[1].match(/^\s*pdd-skills:\s*["']?(\d[\d.]*)/m)?.[1] ?? null;
  } catch { return null; }
}

function detectClaudePluginReadOnly({ home, claudeConfigDir, fs }) {
  const claudeBase = claudeConfigDir && isAbsolute(claudeConfigDir)
    ? claudeConfigDir
    : (home ? join(home, '.claude') : '');
  if (!claudeBase) return null;
  const pluginsFile = join(claudeBase, 'plugins', 'installed_plugins.json');
  const parsed = readJsonBounded(pluginsFile, fs);
  if (!parsed) return null;
  const entries = isPlainObject(parsed.plugins) ? parsed.plugins : parsed;
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
    } else if (isPlainObject(value)) {
      return value.installPath ?? pluginsFile;
    } else if (value) {
      return pluginsFile;
    }
  }
  return null;
}

function hasSkillFile(root, name, fs) {
  try { return fs.statSync(join(root, name, 'SKILL.md')).isFile(); } catch { return false; }
}

function inspectRetiredSkill(root, name, fs) {
  const dir = join(root, name);
  try {
    const st = fs.lstatSync ? fs.lstatSync(dir) : fs.statSync(dir);
    if (!st.isDirectory()) return null;
  } catch { return null; }
  const hasMarker = (() => {
    try { return (fs.lstatSync ?? fs.statSync)(join(dir, SKILL_MARKER)).isFile(); } catch { return false; }
  })();
  if (hasMarker) return { name, marked: true };
  if (hasSkillFile(root, name, fs)) return { name, marked: false };
  return null;
}

function inspectSkillEntry(dir, bundledVersion, bundledDigest, fs) {
  let markerText = null;
  try { markerText = fs.readFileSync(join(dir, SKILL_MARKER), 'utf8'); } catch { /* Unmarked copy. */ }
  if (markerText !== null) {
    let marker;
    try { marker = JSON.parse(markerText); } catch { return { state: 'differs', version: null, marked: true }; }
    const markerVersion = typeof marker?.version === 'string' ? marker.version : null;
    const cmp = compareSemver(markerVersion, bundledVersion);
    if (cmp !== null && cmp < 0) return { state: 'older', version: markerVersion, marked: true };
    if (cmp === 0 && marker?.digest !== bundledDigest) return { state: 'differs', version: markerVersion, marked: true };
    if (cmp === null) return { state: 'differs', version: markerVersion, marked: true };
    return { state: 'current', version: markerVersion, marked: true };
  }
  try {
    if (bundledDigest && digestDir(dir, fs) === bundledDigest) {
      return { state: 'current', version: bundledVersion, marked: false };
    }
  } catch { /* Fall back to frontmatter version. */ }
  const fmVer = readSkillFrontmatterVersion(dir, fs);
  const cmp = compareSemver(fmVer, bundledVersion);
  if (cmp !== null && cmp < 0) return { state: 'older', version: fmVer, marked: false };
  if (cmp !== null && cmp > 0) return { state: 'current', version: fmVer, marked: false };
  return { state: 'differs', version: fmVer, marked: false };
}

function checkSkillsHealth({ packageRoot, env, home, fs, platform, pddVersion }) {
  const claudeConfigDir = typeof env?.CLAUDE_CONFIG_DIR === 'string' && env.CLAUDE_CONFIG_DIR.trim() && isAbsolute(env.CLAUDE_CONFIG_DIR.trim())
    ? env.CLAUDE_CONFIG_DIR.trim()
    : null;
  const codexHome = typeof env?.CODEX_HOME === 'string' && env.CODEX_HOME.trim() && isAbsolute(env.CODEX_HOME.trim())
    ? env.CODEX_HOME.trim()
    : null;

  if (!home && !claudeConfigDir && !codexHome) {
    return {
      check: { status: 'ok', claude_plugin: null, roots: [], remediations: [] },
      findings: [],
    };
  }

  let bundledSkills = [];
  try {
    bundledSkills = PDD_SKILL_NAMES.map(name => {
      const source = join(packageRoot, 'skills', name);
      return { name, source, digest: safeExists(source, fs) ? digestDir(source, fs) : null };
    });
  } catch { bundledSkills = PDD_SKILL_NAMES.map(name => ({ name, source: null, digest: null })); }

  const claudeBase = claudeConfigDir ?? (home ? join(home, '.claude') : null);
  const claudePlugin = detectClaudePluginReadOnly({ home, claudeConfigDir, fs });

  const antigravityDetected = Boolean(home) && (
    safeExists(join(home, '.gemini', 'antigravity-cli'), fs)
    || safeExists(join(home, '.gemini', 'config', 'mcp_config.json'), fs)
    || executableOnPath('agy', env, fs, platform)
  );
  const geminiDetected = (Boolean(home) && safeExists(join(home, '.gemini', 'settings.json'), fs))
    || executableOnPath('gemini', env, fs, platform);
  const claudeDetected = Boolean(claudeBase && safeExists(claudeBase, fs))
    || Boolean(claudeConfigDir ? safeExists(join(claudeConfigDir, '.claude.json'), fs) : (home && safeExists(join(home, '.claude.json'), fs)))
    || executableOnPath('claude', env, fs, platform);
  const codexDetected = Boolean((codexHome ?? (home ? join(home, '.codex') : null)) && safeExists(codexHome ?? join(home, '.codex'), fs))
    || executableOnPath('codex', env, fs, platform);

  const candidates = [
    ...(home ? [{ agent: 'Codex / Gemini', root: join(home, '.agents', 'skills'), primary: true, required: codexDetected || geminiDetected }] : []),
    ...(claudeBase ? [{ agent: 'Claude Code', root: join(claudeBase, 'skills'), primary: true, required: claudeDetected && !claudePlugin, pluginManaged: claudePlugin }] : []),
    ...(home ? [{ agent: 'Antigravity', root: join(home, '.gemini', 'config', 'skills'), primary: false, required: antigravityDetected }] : []),
    ...(home ? [{ agent: 'Codex (legacy)', root: join(home, '.codex', 'skills'), primary: false, required: false }] : []),
    ...(codexHome ? [{ agent: 'Codex (CODEX_HOME)', root: join(codexHome, 'skills'), primary: false, required: false }] : []),
  ];

  const seenCanon = new Set();
  const roots = [];
  const findings = [];
  const remediations = new Set();
  let anyCurrent = Boolean(claudePlugin);

  const pushRetiredFindings = (rootPath, retiredEntries) => {
    const marked = retiredEntries.filter(r => r.marked).map(r => r.name);
    const unmarked = retiredEntries.filter(r => !r.marked).map(r => r.name);
    if (marked.length > 0) {
      remediations.add('pdd setup');
      findings.push({
        check: 'skills',
        severity: 'warn',
        code: 'skills-retired',
        message: `${cleanText(shortenHomePath(rootPath, home))} has retired PDD skills: ${marked.join(', ')}`,
        path: rootPath,
        remediation: 'pdd setup',
      });
    }
    if (unmarked.length > 0) {
      const rmTargets = unmarked.map(name => safeQuotePath(join(rootPath, name))).join(' ');
      const fix = `rm -rf ${rmTargets}`;
      remediations.add(fix);
      findings.push({
        check: 'skills',
        severity: 'warn',
        code: 'skills-retired',
        message: `${cleanText(shortenHomePath(rootPath, home))} has unmarked retired PDD skills: ${unmarked.join(', ')}`,
        path: rootPath,
        remediation: fix,
      });
    }
    if (marked.length > 0 && unmarked.length === 0) return 'pdd setup';
    if (unmarked.length > 0) return `rm -rf ${unmarked.map(name => safeQuotePath(join(rootPath, name))).join(' ')}`;
    return null;
  };

  for (const item of candidates) {
    const canon = normPath(safeRealpath(item.root, fs), platform);
    if (seenCanon.has(canon)) continue;
    seenCanon.add(canon);

    const retiredEntries = RETIRED_SKILL_NAMES.map(name => inspectRetiredSkill(item.root, name, fs)).filter(Boolean);
    const retiredNames = retiredEntries.map(r => r.name);

    if (item.pluginManaged) {
      const remediation = retiredEntries.length > 0 ? pushRetiredFindings(item.root, retiredEntries) : null;
      roots.push({
        agent: item.agent,
        root: item.root,
        status: retiredEntries.length > 0 ? 'retired' : 'plugin-managed',
        version: pddVersion,
        stale: null,
        stale_skills: [],
        retired_skills: retiredNames,
        remediation,
      });
      continue;
    }

    const presentSkills = bundledSkills.filter(skill => hasSkillFile(item.root, skill.name, fs));
    const rootExists = safeExists(item.root, fs);

    if (presentSkills.length === 0) {
      if (retiredEntries.length > 0) {
        const remediation = pushRetiredFindings(item.root, retiredEntries);
        roots.push({
          agent: item.agent,
          root: item.root,
          status: 'retired',
          version: null,
          stale: null,
          stale_skills: [],
          retired_skills: retiredNames,
          remediation,
        });
      } else if (item.required) {
        remediations.add('pdd setup');
        roots.push({
          agent: item.agent,
          root: item.root,
          status: 'missing',
          version: null,
          stale: null,
          stale_skills: [],
          retired_skills: [],
          remediation: 'pdd setup',
        });
        findings.push({
          check: 'skills',
          severity: 'warn',
          code: 'skills-missing',
          message: `${item.agent} PDD skill missing in ${cleanText(shortenHomePath(item.root, home))}`,
          path: item.root,
          remediation: 'pdd setup',
        });
      } else if (item.primary || rootExists) {
        roots.push({
          agent: item.agent,
          root: item.root,
          status: 'absent',
          version: null,
          stale: null,
          stale_skills: [],
          retired_skills: [],
          remediation: null,
        });
      }
      continue;
    }

    const staleSkills = [];
    let observedVersion = pddVersion;
    for (const skill of bundledSkills) {
      if (!hasSkillFile(item.root, skill.name, fs)) {
        staleSkills.push({ name: skill.name, state: 'missing', version: null, marked: true });
        continue;
      }
      const res = inspectSkillEntry(join(item.root, skill.name), pddVersion, skill.digest, fs);
      if (res.version) observedVersion = res.version;
      if (res.state !== 'current') {
        staleSkills.push({ name: skill.name, state: res.state, version: res.version, marked: res.marked });
      }
    }

    if (staleSkills.length === 0 && retiredEntries.length === 0) {
      anyCurrent = true;
      roots.push({
        agent: item.agent,
        root: item.root,
        status: 'current',
        version: observedVersion,
        stale: null,
        stale_skills: [],
        retired_skills: [],
        remediation: null,
      });
    } else {
      const staleKind = staleSkills.length === 0
        ? null
        : staleSkills.every(s => s.state === 'older') ? 'older' : 'differs';
      const staleRemediation = staleSkills.length > 0
        ? (staleSkills.every(s => !s.marked) ? 'npx skills add promptdriven/pdd -g' : 'pdd setup')
        : null;
      if (staleRemediation) {
        remediations.add(staleRemediation);
        const desc = staleSkills.map(s => `${s.name} ${s.state}${s.version ? ` (${cleanText(s.version)})` : ''}`).join(', ');
        findings.push({
          check: 'skills',
          severity: 'warn',
          code: 'skills-stale',
          message: `${cleanText(shortenHomePath(item.root, home))}: ${desc}`,
          path: item.root,
          remediation: staleRemediation,
        });
      }
      const retiredRemediation = retiredEntries.length > 0 ? pushRetiredFindings(item.root, retiredEntries) : null;
      roots.push({
        agent: item.agent,
        root: item.root,
        status: staleSkills.length > 0 ? 'stale' : 'retired',
        version: observedVersion,
        stale: staleKind,
        stale_skills: staleSkills.map(({ name, state, version }) => ({ name, state, version })),
        retired_skills: retiredNames,
        remediation: staleRemediation ?? retiredRemediation,
      });
    }
  }

  // If NO user skill folder (and no Claude plugin) has a current pdd skill, flag missing skills cleanly.
  if (!anyCurrent && findings.length === 0 && home) {
    const defaultRoot = join(home, '.agents', 'skills');
    remediations.add('pdd setup');
    findings.push({
      check: 'skills',
      severity: 'warn',
      code: 'skills-missing',
      message: `No installed PDD skill found (expected in ${cleanText(shortenHomePath(defaultRoot, home))})`,
      path: defaultRoot,
      remediation: 'pdd setup',
    });
  }

  return {
    check: {
      status: findings.length === 0 ? 'ok' : 'warn',
      claude_plugin: claudePlugin,
      roots,
      remediations: [...remediations],
    },
    findings,
  };
}

function checkSymlinkWithinBoundary(file, boundaryDir, fs, platform) {
  const target = resolve(file);
  const stopAt = resolve(boundaryDir);
  let current = target;
  const lstat = fs.lstatSync ?? fs.statSync;
  while (true) {
    try {
      const st = lstat(current);
      if (st.isSymbolicLink?.()) return { isSymlink: true, symlinkPath: current };
      if (normPath(current, platform) === normPath(target, platform) && !st.isFile()) return { isSymlink: false, nonRegular: true };
    } catch (error) {
      if (error?.code !== 'ENOENT') return { isSymlink: false, unreadable: error?.code ?? error?.message ?? 'unreadable' };
    }
    if (normPath(current, platform) === normPath(stopAt, platform)) break;
    const parent = dirname(current);
    if (parent === current) break;
    current = parent;
  }
  return { isSymlink: false, nonRegular: false, unreadable: null };
}

function extractMcpPddBin(entry) {
  if (!isPlainObject(entry)) return { hasMcpArg: false, command: '', bin: null };
  const cmd = typeof entry.command === 'string' ? entry.command.trim() : '';
  const args = Array.isArray(entry.args) ? entry.args.map(String) : [];
  const hasMcpArg = args.includes('mcp');
  const argBin = args.find(arg => /(?:^|[\\/])pdd(?:\.(?:mjs|cmd|exe))?$/i.test(arg));
  if (argBin) return { hasMcpArg, command: cmd, bin: argBin };
  if (/(?:^|[\\/])pdd(?:\.(?:mjs|cmd|exe))?$/i.test(cmd) || /^pdd(?:\.(?:cmd|exe))?$/i.test(cmd)) {
    return { hasMcpArg, command: cmd, bin: cmd };
  }
  return { hasMcpArg, command: cmd, bin: null };
}

function checkMcpHealth({ cwd, env, home, fs, platform, installDiagnosis }) {
  const codexEnv = typeof env?.CODEX_HOME === 'string' && env.CODEX_HOME.trim() ? resolve(cwd, env.CODEX_HOME.trim()) : null;
  const claudeEnv = typeof env?.CLAUDE_CONFIG_DIR === 'string' && env.CLAUDE_CONFIG_DIR.trim() ? resolve(cwd, env.CLAUDE_CONFIG_DIR.trim()) : null;

  const codex = codexEnv ?? (home ? join(home, '.codex') : null);
  const claudeDir = claudeEnv ?? (home ? join(home, '.claude') : null);
  const claudeFile = claudeEnv ? join(claudeEnv, '.claude.json') : (home ? join(home, '.claude.json') : null);
  const geminiFile = home ? join(home, '.gemini', 'settings.json') : null;
  const agyDir = home ? join(home, '.gemini', 'config') : null;
  const agyFile = agyDir ? join(agyDir, 'mcp_config.json') : null;

  const candidates = [
    ...(codex ? [{
      name: 'Codex',
      file: join(codex, 'config.toml'),
      boundary: codex,
      toml: true,
      detected: safeExists(codex, fs) || safeExists(join(codex, 'config.toml'), fs) || executableOnPath('codex', env, fs, platform),
    }] : []),
    ...(claudeFile ? [{
      name: 'Claude Code',
      file: claudeFile,
      boundary: claudeEnv ? claudeDir : claudeFile,
      toml: false,
      detected: Boolean(claudeDir && safeExists(claudeDir, fs)) || safeExists(claudeFile, fs) || executableOnPath('claude', env, fs, platform),
    }] : []),
    ...(geminiFile ? [{
      name: 'Gemini CLI',
      file: geminiFile,
      boundary: join(home, '.gemini'),
      toml: false,
      detected: safeExists(geminiFile, fs) || executableOnPath('gemini', env, fs, platform),
    }] : []),
    ...(agyFile ? [{
      name: 'Antigravity',
      file: agyFile,
      boundary: agyDir,
      toml: false,
      detected: safeExists(agyFile, fs) || safeExists(join(home, '.gemini', 'antigravity-cli'), fs) || executableOnPath('agy', env, fs, platform),
    }] : []),
  ].filter(item => item.detected);

  const currentReal = normPath(installDiagnosis.current.realPath, platform);
  const agents = [];
  const findings = [];
  const remediations = new Set();

  for (const candidate of candidates) {
    const shortFile = cleanText(shortenHomePath(candidate.file, home));
    const pathCheck = checkSymlinkWithinBoundary(candidate.file, candidate.boundary, fs, platform);
    if (pathCheck.isSymlink) {
      agents.push({
        name: candidate.name,
        file: candidate.file,
        status: 'symlink',
        configured_bin: null,
        detail: `${cleanText(shortenHomePath(pathCheck.symlinkPath, home))} is a symlink (skipped by pdd setup)`,
        remediation: null,
      });
      findings.push({
        check: 'mcp',
        severity: 'advisory',
        code: 'mcp-symlink',
        message: `${candidate.name} (${shortFile}): symlinked config (register PDD MCP manually or use a regular file)`,
        path: candidate.file,
        remediation: null,
      });
      continue;
    }
    if (pathCheck.nonRegular) {
      const fix = `Move or remove non-regular path ${shortFile}, then run: pdd setup --yes`;
      remediations.add(fix);
      agents.push({
        name: candidate.name,
        file: candidate.file,
        status: 'non-regular',
        configured_bin: null,
        detail: `${shortFile} is not a regular file`,
        remediation: fix,
      });
      findings.push({
        check: 'mcp',
        severity: 'error',
        code: 'mcp-non-regular',
        message: `${candidate.name} (${shortFile}): config path is not a regular file`,
        path: candidate.file,
        remediation: fix,
      });
      continue;
    }
    if (pathCheck.unreadable) {
      const fix = `Check file permissions on ${shortFile}, then run: pdd setup`;
      agents.push({
        name: candidate.name,
        file: candidate.file,
        status: 'unreadable',
        configured_bin: null,
        detail: `unreadable (${cleanText(pathCheck.unreadable)})`,
        remediation: fix,
      });
      remediations.add(fix);
      findings.push({
        check: 'mcp',
        severity: 'error',
        code: 'mcp-unreadable',
        message: `${candidate.name} (${shortFile}): unreadable (${cleanText(pathCheck.unreadable)})`,
        path: candidate.file,
        remediation: fix,
      });
      continue;
    }

    if (!safeExists(candidate.file, fs)) {
      remediations.add('pdd setup --yes');
      agents.push({
        name: candidate.name,
        file: candidate.file,
        status: 'missing',
        configured_bin: null,
        detail: 'config file not created yet',
        remediation: 'pdd setup --yes',
      });
      findings.push({
        check: 'mcp',
        severity: 'warn',
        code: 'mcp-missing',
        message: `${candidate.name} (${shortFile}): PDD MCP not registered`,
        path: candidate.file,
        remediation: 'pdd setup --yes',
      });
      continue;
    }

    let raw;
    try {
      const st = fs.statSync(candidate.file);
      if (st.size > MAX_CONFIG_BYTES) {
        const fix = `Inspect oversized config ${shortFile}`;
        remediations.add(fix);
        agents.push({ name: candidate.name, file: candidate.file, status: 'unreadable', configured_bin: null, detail: 'config exceeds 2 MiB limit', remediation: fix });
        findings.push({ check: 'mcp', severity: 'error', code: 'mcp-unreadable', message: `${candidate.name} (${shortFile}): config exceeds 2 MiB limit`, path: candidate.file, remediation: fix });
        continue;
      }
      raw = fs.readFileSync(candidate.file, 'utf8');
    } catch (error) {
      const fix = `Check file permissions on ${shortFile}, then run: pdd setup`;
      remediations.add(fix);
      agents.push({ name: candidate.name, file: candidate.file, status: 'unreadable', configured_bin: null, detail: cleanText(error?.code ?? 'read failed'), remediation: fix });
      findings.push({ check: 'mcp', severity: 'error', code: 'mcp-unreadable', message: `${candidate.name} (${shortFile}): unreadable`, path: candidate.file, remediation: fix });
      continue;
    }

    if (!candidate.toml && raw.trim().length === 0) {
      const fix = `Fix or remove empty ${shortFile}, then run: pdd setup --yes`;
      remediations.add(fix);
      agents.push({ name: candidate.name, file: candidate.file, status: 'empty', configured_bin: null, detail: '0-byte / empty JSON file', remediation: fix });
      findings.push({ check: 'mcp', severity: 'error', code: 'mcp-empty', message: `${candidate.name} (${shortFile}): 0-byte / empty JSON file`, path: candidate.file, remediation: fix });
      continue;
    }

    let data;
    try {
      data = candidate.toml ? parseToml(raw) : JSON.parse(raw);
    } catch {
      const kindLabel = candidate.toml ? 'TOML' : 'JSON';
      const fix = `Fix malformed ${kindLabel} in ${shortFile}, then run: pdd setup`;
      remediations.add(fix);
      agents.push({ name: candidate.name, file: candidate.file, status: 'malformed', configured_bin: null, detail: `malformed ${kindLabel}`, remediation: fix });
      findings.push({ check: 'mcp', severity: 'error', code: 'mcp-malformed', message: `${candidate.name} (${shortFile}): malformed ${kindLabel}`, path: candidate.file, remediation: fix });
      continue;
    }

    const key = candidate.toml ? 'mcp_servers' : 'mcpServers';
    if (!isPlainObject(data) || (data[key] !== undefined && !isPlainObject(data[key]))) {
      const fix = `Fix invalid ${key} structure in ${shortFile}, then run: pdd setup`;
      remediations.add(fix);
      agents.push({ name: candidate.name, file: candidate.file, status: 'malformed', configured_bin: null, detail: `invalid ${key} structure`, remediation: fix });
      findings.push({ check: 'mcp', severity: 'error', code: 'mcp-malformed', message: `${candidate.name} (${shortFile}): invalid ${key} structure`, path: candidate.file, remediation: fix });
      continue;
    }

    const entry = data[key]?.pdd;
    if (entry === undefined) {
      remediations.add('pdd setup --yes');
      agents.push({ name: candidate.name, file: candidate.file, status: 'missing', configured_bin: null, detail: 'pdd MCP entry missing', remediation: 'pdd setup --yes' });
      findings.push({ check: 'mcp', severity: 'warn', code: 'mcp-missing', message: `${candidate.name} (${shortFile}): PDD MCP not registered`, path: candidate.file, remediation: 'pdd setup --yes' });
      continue;
    }

    const { hasMcpArg, command, bin } = extractMcpPddBin(entry);
    if (!hasMcpArg || !bin || !command) {
      remediations.add('pdd setup --yes');
      const detail = !command ? 'missing command in pdd MCP entry' : 'pdd MCP entry does not point to pdd mcp';
      agents.push({ name: candidate.name, file: candidate.file, status: 'stale', configured_bin: bin, detail, remediation: 'pdd setup --yes' });
      findings.push({ check: 'mcp', severity: 'warn', code: 'mcp-stale', message: `${candidate.name} (${shortFile}): ${detail}`, path: candidate.file, remediation: 'pdd setup --yes' });
      continue;
    }

    // Verify absolute runtime command (e.g. Node binary) still exists when args invoke bin/pdd.mjs.
    const isAbsCmd = platform === 'win32' ? (/^[A-Za-z]:[\\/]/.test(command) || isAbsolute(command)) : isAbsolute(command);
    if (isAbsCmd && normPath(command, platform) !== normPath(bin, platform) && !safeExists(command, fs)) {
      const detail = `command binary missing: ${cleanText(shortenHomePath(command, home))}`;
      remediations.add('pdd setup --yes');
      agents.push({ name: candidate.name, file: candidate.file, status: 'stale', configured_bin: bin, detail, remediation: 'pdd setup --yes' });
      findings.push({ check: 'mcp', severity: 'warn', code: 'mcp-stale', message: `${candidate.name} (${shortFile}): ${detail}`, path: candidate.file, remediation: 'pdd setup --yes' });
      continue;
    }

    if (/^pdd(?:\.(?:cmd|exe))?$/i.test(bin)) {
      if (installDiagnosis.hasConflict || !installDiagnosis.pathSelected?.isCurrent) {
        const detail = !installDiagnosis.pathSelected
          ? `unpinned "${cleanText(bin)}" command but pdd is not on PATH`
          : `unpinned "${cleanText(bin)}" command while competing installs exist`;
        remediations.add('pdd setup --yes');
        agents.push({ name: candidate.name, file: candidate.file, status: 'stale', configured_bin: bin, detail, remediation: 'pdd setup --yes' });
        findings.push({ check: 'mcp', severity: 'warn', code: 'mcp-stale', message: `${candidate.name} (${shortFile}): ${detail}`, path: candidate.file, remediation: 'pdd setup --yes' });
      } else {
        agents.push({ name: candidate.name, file: candidate.file, status: 'ok', configured_bin: bin, detail: null, remediation: null });
      }
      continue;
    }

    const exists = safeExists(bin, fs);
    const resolved = exists ? resolveCanonicalPddTarget(bin, { fs, env, home, platform }) : { realPath: bin };
    const matchesCurrent = exists && normPath(resolved.realPath, platform) === currentReal;
    if (!matchesCurrent) {
      const detail = exists
        ? `points to ${cleanText(shortenHomePath(bin, home))} instead of ${cleanText(shortenHomePath(installDiagnosis.current.path, home))}`
        : `points to missing binary ${cleanText(shortenHomePath(bin, home))}`;
      remediations.add('pdd setup --yes');
      agents.push({ name: candidate.name, file: candidate.file, status: 'stale', configured_bin: bin, detail, remediation: 'pdd setup --yes' });
      findings.push({ check: 'mcp', severity: 'warn', code: 'mcp-stale', message: `${candidate.name} (${shortFile}): ${detail}`, path: candidate.file, remediation: 'pdd setup --yes' });
      continue;
    }

    agents.push({ name: candidate.name, file: candidate.file, status: 'ok', configured_bin: bin, detail: null, remediation: null });
  }

  const actionable = findings.filter(f => f.severity !== 'advisory');
  return {
    check: {
      status: actionable.length > 0 ? 'warn' : (findings.length > 0 ? 'advisory' : 'ok'),
      agents,
      remediations: [...remediations],
    },
    findings,
  };
}

function hasGhHostsConfig(env, home, fs, platform) {
  const dirs = [];
  if (env?.GH_CONFIG_DIR && env.GH_CONFIG_DIR.trim()) dirs.push(env.GH_CONFIG_DIR.trim());
  else if (env?.XDG_CONFIG_HOME && env.XDG_CONFIG_HOME.trim()) dirs.push(join(env.XDG_CONFIG_HOME.trim(), 'gh'));
  else {
    if (platform === 'win32' && env?.APPDATA && env.APPDATA.trim()) {
      dirs.push(join(env.APPDATA.trim(), 'GitHub CLI'));
    }
    if (home) dirs.push(join(home, '.config', 'gh'));
  }
  return dirs.some(dir => safeExists(join(dir, 'hosts.yml'), fs));
}

function checkGhHealth({ cwd, env, home, fs, spawnImpl, platform, timeout }) {
  if ((env?.GH_TOKEN && env.GH_TOKEN.trim()) || (env?.GITHUB_TOKEN && env.GITHUB_TOKEN.trim())) {
    return {
      check: { status: 'ok', installed: true, authenticated: true, method: 'env-token', advisory: null, remediation: null },
      findings: [],
    };
  }
  const hasGh = executableOnPath('gh', env, fs, platform);
  if (!hasGh) {
    const advisory = 'gh CLI not installed (optional; needed for hosted pdd test / pdd <PROMPT.md|STORY>)';
    const remediation = 'Install GitHub CLI (https://cli.github.com) and run: gh auth login';
    return {
      check: { status: 'advisory', installed: false, authenticated: false, method: 'missing', advisory, remediation },
      findings: [{ check: 'gh', severity: 'advisory', code: 'gh-missing', message: advisory, path: null, remediation }],
    };
  }
  // Never spawn `gh` when hosts.yml is absent, because `gh` creates ~/.local/state/gh on startup.
  if (!hasGhHostsConfig(env, home, fs, platform)) {
    const advisory = 'not signed in (optional; needed for hosted pdd test / pdd <PROMPT.md|STORY>)';
    return {
      check: { status: 'advisory', installed: true, authenticated: false, method: 'signed-out', advisory, remediation: 'gh auth login' },
      findings: [{ check: 'gh', severity: 'advisory', code: 'gh-signed-out', message: advisory, path: null, remediation: 'gh auth login' }],
    };
  }
  try {
    const childEnv = { ...env, ...(home ? { HOME: home } : {}), GH_NO_UPDATE_NOTIFIER: '1' };
    const reply = spawnImpl('gh', ['auth', 'token'], {
      cwd,
      env: childEnv,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
      timeout,
      maxBuffer: 65536,
    });
    const timedOut = reply?.error?.code === 'ETIMEDOUT' || reply?.signal === 'SIGTERM' || reply?.signal === 'SIGKILL';
    if (timedOut) {
      const advisory = 'gh auth check timed out';
      return {
        check: { status: 'advisory', installed: true, authenticated: false, method: 'timeout', advisory, remediation: 'gh auth status' },
        findings: [{ check: 'gh', severity: 'advisory', code: 'gh-timeout', message: advisory, path: null, remediation: 'gh auth status' }],
      };
    }
    if (!reply?.error && reply?.status === 0 && Boolean(reply?.stdout?.trim())) {
      return {
        check: { status: 'ok', installed: true, authenticated: true, method: 'gh-auth', advisory: null, remediation: null },
        findings: [],
      };
    }
  } catch { /* Treat failed probe as signed out. */ }

  const advisory = 'not signed in (optional; needed for hosted pdd test / pdd <PROMPT.md|STORY>)';
  return {
    check: { status: 'advisory', installed: true, authenticated: false, method: 'signed-out', advisory, remediation: 'gh auth login' },
    findings: [{ check: 'gh', severity: 'advisory', code: 'gh-signed-out', message: advisory, path: null, remediation: 'gh auth login' }],
  };
}

export function collectDoctorReport(options = {}, ports = {}) {
  const fs = ports.fs ?? options.fs ?? nativeFs;
  const spawnImpl = ports.spawnSync ?? options.spawnSync ?? nativeSpawnSync;
  const platform = ports.platform ?? options.platform ?? process.platform;
  const homedirFn = ports.homedir ?? options.homedir ?? nativeHomedir;
  const env = options.env ?? process.env;
  const cwd = options.cwd ?? process.cwd();
  const home = resolveSafeHome(options.home, env, homedirFn, platform);
  const packageRoot = options.packageRoot ?? PACKAGE_ROOT;
  const timeout = Math.min(5000, Math.max(100, Number(options.probeTimeoutMs ?? DEFAULT_TIMEOUT_MS) || DEFAULT_TIMEOUT_MS));
  const nodeVersion = String(ports.nodeVersion ?? options.nodeVersion ?? process.versions.node).replace(/^v/, '');

  const findings = [];

  // 1. Host installs & cross-shell PATH parity (also tells us running version, kind & canonical bin)
  const installDiagnosis = (ports.diagnoseHostInstalls ?? diagnoseHostInstalls)(
    {
      packageRoot,
      currentBin: options.currentBin,
      cwd,
      env,
      home,
      checkLoginShells: options.checkLoginShells ?? ports.checkLoginShells ?? true,
      probeTimeoutMs: timeout,
      ...(options.systemRoots !== undefined ? { systemRoots: options.systemRoots } : {}),
      ...(ports.systemRoots !== undefined ? { systemRoots: ports.systemRoots } : {}),
      ...(options.loginShells !== undefined ? { loginShells: options.loginShells } : {}),
      ...(ports.loginShells !== undefined ? { loginShells: ports.loginShells } : {}),
    },
    { fs, spawnSync: spawnImpl, platform, uid: ports.uid, homedir: homedirFn },
  );

  // 1a. Runtime & Node version check
  const pddVersion = installDiagnosis.current.version;
  const nodeCmp = compareSemver(nodeVersion, MIN_NODE_VERSION);
  const nodeCompatible = nodeCmp !== null && nodeCmp >= 0;
  const runtimeRemediation = !nodeCompatible
    ? `Install Node.js >= ${MIN_NODE_VERSION} (https://nodejs.org)`
    : (!pddVersion ? 'npm install -g @promptdriven/pdd && pdd setup' : null);

  if (!nodeCompatible) {
    findings.push({
      check: 'runtime',
      severity: 'error',
      code: 'node-incompatible',
      message: `Node.js v${cleanText(nodeVersion)} is older than required >= ${MIN_NODE_VERSION}`,
      path: null,
      remediation: runtimeRemediation,
    });
  }
  if (!pddVersion) {
    findings.push({
      check: 'runtime',
      severity: 'error',
      code: 'cli-version-unreadable',
      message: `Could not read pdd package version at ${cleanText(shortenHomePath(packageRoot, home))}`,
      path: packageRoot,
      remediation: runtimeRemediation,
    });
  }

  const runtimeCheck = {
    status: nodeCompatible && Boolean(pddVersion) ? 'ok' : 'error',
    pdd_version: pddVersion,
    node_version: nodeVersion,
    min_node_version: MIN_NODE_VERSION,
    node_compatible: nodeCompatible,
    install_kind: installDiagnosis.current.kind,
    current_bin: installDiagnosis.current.path,
    package_root: installDiagnosis.current.packageRoot,
    remediation: runtimeRemediation,
  };

  // 2. Installs & PATH findings
  const installRemediations = new Set();
  for (const dup of installDiagnosis.duplicates) {
    if (dup.remediation) installRemediations.add(dup.remediation);
    const verText = dup.version ? cleanText(dup.version) : (dup.versionTimedOut ? 'version timed out' : 'version unknown');
    findings.push({
      check: 'installs',
      severity: dup.shadowsCurrent ? 'error' : 'warn',
      code: dup.shadowsCurrent ? 'path-shadowed' : 'duplicate-install',
      message: `${dup.shadowsCurrent ? 'PATH shadowed by' : 'Duplicate pdd install:'} ${cleanText(shortenHomePath(dup.path, home))} (${verText}, ${cleanText(dup.kind)})`,
      path: dup.path,
      remediation: dup.remediation,
    });
  }
  for (const split of installDiagnosis.shellSplits) {
    if (split.remediation) installRemediations.add(split.remediation);
    const verText = split.version ? ` (${cleanText(split.version)})` : '';
    const currVer = pddVersion ? ` (${cleanText(pddVersion)})` : '';
    findings.push({
      check: 'installs',
      severity: 'error',
      code: 'login-shell-split',
      message: `${cleanText(split.name)} -lc resolves ${cleanText(shortenHomePath(split.resolvedPath, home))}${verText} instead of ${cleanText(shortenHomePath(installDiagnosis.current.path, home))}${currVer}`,
      path: split.resolvedPath,
      remediation: split.remediation,
    });
  }
  if (installDiagnosis.unscopedNpm.foreign) {
    installRemediations.add(installDiagnosis.unscopedNpm.remediation);
    findings.push({
      check: 'installs',
      severity: 'error',
      code: 'unscoped-npm-foreign',
      message: `Unrelated npm package "pdd" at ${cleanText(shortenHomePath(installDiagnosis.unscopedNpm.foreign, home))}`,
      path: installDiagnosis.unscopedNpm.foreign,
      remediation: installDiagnosis.unscopedNpm.remediation,
    });
  }
  if (installDiagnosis.unscopedNpm.legacy) {
    installRemediations.add(installDiagnosis.unscopedNpm.remediation);
    findings.push({
      check: 'installs',
      severity: 'error',
      code: 'unscoped-npm-legacy',
      message: `Legacy unscoped npm package "pdd" at ${cleanText(shortenHomePath(installDiagnosis.unscopedNpm.legacy, home))}`,
      path: installDiagnosis.unscopedNpm.legacy,
      remediation: installDiagnosis.unscopedNpm.remediation,
    });
  }

  const installsCheck = {
    status: installDiagnosis.hasConflict ? 'warn' : 'ok',
    current: installDiagnosis.current,
    installs: installDiagnosis.installs,
    duplicates: installDiagnosis.duplicates,
    path_selected: installDiagnosis.pathSelected,
    shadowed_on_path: installDiagnosis.shadowedOnPath,
    unscoped_npm: installDiagnosis.unscopedNpm,
    login_shells: installDiagnosis.loginShells,
    shell_splits: installDiagnosis.shellSplits,
    remediations: [...installRemediations],
  };

  // 3. Agent skills health
  const skillsRes = checkSkillsHealth({ packageRoot, env, home, fs, platform, pddVersion: pddVersion ?? '0.0.0' });
  findings.push(...skillsRes.findings);

  // 4. Agent MCP config health
  const mcpRes = checkMcpHealth({ cwd, env, home, fs, platform, installDiagnosis });
  findings.push(...mcpRes.findings);

  // 5. GitHub CLI (gh) sign-in health (advisory only)
  const ghRes = checkGhHealth({ cwd, env, home, fs, spawnImpl, platform, timeout });
  findings.push(...ghRes.findings);

  const actionableFindings = findings.filter(f => f.severity === 'error' || f.severity === 'warn');
  const advisoryFindings = findings.filter(f => f.severity === 'advisory');
  const exitCode = actionableFindings.length > 0 ? 1 : 0;

  const allRemediations = [];
  for (const f of actionableFindings) {
    if (f.remediation && !allRemediations.includes(f.remediation)) allRemediations.push(f.remediation);
  }

  return {
    schema_version: 'pdd.doctor.v1',
    ok: exitCode === 0,
    exit_code: exitCode,
    summary: {
      issues: actionableFindings.length,
      advisories: advisoryFindings.length,
    },
    checks: {
      runtime: runtimeCheck,
      installs: installsCheck,
      skills: skillsRes.check,
      mcp: mcpRes.check,
      gh: ghRes.check,
    },
    findings,
    remediations: allRemediations,
  };
}

export function formatDoctorReport(report, { home } = {}) {
  const fmt = p => cleanText(shortenHomePath(p, home));
  const { runtime, installs, skills, mcp, gh } = report.checks;
  const safeVersion = cleanText(runtime.pdd_version ?? 'unknown');
  const lines = [`pdd doctor (${safeVersion})`, ''];

  // 1. CLI & Node
  const runtimeIcon = runtime.status === 'ok' ? '✓' : '⚠';
  const displayCurrentBin = installs.installs.find(i => i.isCurrent)?.path ?? runtime.current_bin;
  const nodeDetail = runtime.node_compatible
    ? `Node v${cleanText(runtime.node_version)}`
    : `Node v${cleanText(runtime.node_version)} (requires >= ${cleanText(runtime.min_node_version)})`;
  lines.push(`${runtimeIcon} CLI & Node      pdd ${safeVersion} (${cleanText(runtime.install_kind)} · ${fmt(displayCurrentBin)}) · ${nodeDetail}`);
  if (runtime.remediation) lines.push(`    fix: ${cleanText(runtime.remediation)}`);

  // 2. Installs & shell PATH
  const installIcon = installs.status === 'ok' ? '✓' : '⚠';
  if (installs.status === 'ok') {
    const matchedShells = installs.login_shells.filter(s => s.status === 'match').map(s => `${cleanText(s.name)} -lc`);
    const shellText = matchedShells.length > 0 ? `${matchedShells.join(' & ')} match` : 'no conflicts detected';
    lines.push(`${installIcon} Installs & PATH single install · ${shellText}`);
  } else {
    const count = installs.installs.length;
    const splitNote = installs.shell_splits.length > 0
      ? `; ${installs.shell_splits.map(s => `${cleanText(s.name)} -lc`).join(', ')} mismatch`
      : '';
    lines.push(`${installIcon} Installs & PATH ${count} pdd install${count === 1 ? '' : 's'} detected${splitNote}`);
    for (const dup of installs.duplicates) {
      const ver = dup.version ? cleanText(dup.version) : (dup.versionTimedOut ? 'version timed out' : 'version unknown');
      const label = dup.shadowsCurrent ? 'shadowing PATH' : cleanText(dup.kind);
      lines.push(`  • ${fmt(dup.path)} (${ver}, ${label})`);
      if (dup.remediation) lines.push(`    fix: ${cleanText(dup.remediation)}`);
    }
    for (const split of installs.shell_splits) {
      const ver = split.version ? ` (${cleanText(split.version)})` : '';
      const currVer = runtime.pdd_version ? ` (${safeVersion})` : '';
      lines.push(`  • shell split: ${cleanText(split.name)} -lc resolves ${fmt(split.resolvedPath)}${ver} instead of ${fmt(displayCurrentBin)}${currVer}`);
      if (split.remediation && !installs.duplicates.some(d => d.remediation === split.remediation)) {
        lines.push(`    fix: ${cleanText(split.remediation)}`);
      }
    }
    if (installs.unscoped_npm.foreign) {
      lines.push(`  • unrelated npm package "pdd" at ${fmt(installs.unscoped_npm.foreign)}`);
      if (installs.unscoped_npm.remediation) lines.push(`    fix: ${cleanText(installs.unscoped_npm.remediation)}`);
    }
    if (installs.unscoped_npm.legacy) {
      lines.push(`  • unscoped npm package "pdd" at ${fmt(installs.unscoped_npm.legacy)}`);
      if (installs.unscoped_npm.remediation) lines.push(`    fix: ${cleanText(installs.unscoped_npm.remediation)}`);
    }
  }

  // 3. Agent skills
  const skillsIcon = skills.status === 'ok' ? '✓' : '⚠';
  if (skills.status === 'ok') {
    const okParts = skills.roots
      .filter(r => r.status === 'current' || r.status === 'plugin-managed')
      .map(r => r.status === 'plugin-managed' ? `${cleanText(r.agent)} (plugin)` : fmt(r.root));
    lines.push(`${skillsIcon} Agent skills    ${okParts.length ? okParts.join(', ') : 'none configured'} (${safeVersion})`);
  } else {
    const skillFindings = report.findings.filter(f => f.check === 'skills');
    lines.push(`${skillsIcon} Agent skills    ${skillFindings.length} issue${skillFindings.length === 1 ? '' : 's'} found`);
    for (const f of skillFindings) {
      lines.push(`  • ${cleanText(f.message)}`);
      if (f.remediation) lines.push(`    fix: ${cleanText(f.remediation)}`);
    }
  }

  // 4. Agent MCP configs
  const mcpIcon = mcp.status === 'ok' ? '✓' : (mcp.status === 'advisory' ? '–' : '⚠');
  if (mcp.agents.length === 0) {
    lines.push('✓ Agent MCP       no supported coding agents detected');
  } else if (mcp.status === 'ok') {
    const allPinned = mcp.agents.every(a => a.configured_bin && !/^pdd(?:\.(?:cmd|exe))?$/i.test(a.configured_bin));
    lines.push(`${mcpIcon} Agent MCP       ${mcp.agents.map(a => cleanText(a.name)).join(', ')} (${allPinned ? 'pinned to current pdd' : 'configured'})`);
  } else {
    const mcpFindings = report.findings.filter(f => f.check === 'mcp');
    const issueCount = mcpFindings.filter(f => f.severity !== 'advisory').length;
    const summaryLabel = mcp.status === 'advisory'
      ? `${mcpFindings.length} advisory`
      : `${issueCount} issue${issueCount === 1 ? '' : 's'} found`;
    lines.push(`${mcpIcon} Agent MCP       ${summaryLabel}`);
    for (const f of mcpFindings) {
      lines.push(`  • ${cleanText(f.message)}`);
      if (f.remediation) lines.push(`    fix: ${cleanText(f.remediation)}`);
    }
  }

  // 5. GitHub CLI (gh)
  const ghIcon = gh.status === 'ok' ? '✓' : '–';
  if (gh.status === 'ok') {
    lines.push(`${ghIcon} GitHub CLI      gh signed in (ready for hosted interpreter runs)`);
  } else {
    const hint = gh.remediation ? ` — ${cleanText(gh.remediation)}` : '';
    lines.push(`${ghIcon} GitHub CLI      ${cleanText(gh.advisory)}${hint}`);
  }

  lines.push('');
  if (report.ok) {
    lines.push('Healthy: no actionable issues found.');
  } else {
    lines.push(`Found ${report.summary.issues} actionable issue${report.summary.issues === 1 ? '' : 's'}.`);
  }
  return `${lines.join('\n')}\n`;
}

export function runDoctor(options = {}, ports = {}) {
  const env = options.env ?? process.env;
  const platform = ports.platform ?? options.platform ?? process.platform;
  const homedirFn = ports.homedir ?? options.homedir ?? nativeHomedir;
  const home = resolveSafeHome(options.home, env, homedirFn, platform);
  const report = collectDoctorReport({ ...options, home }, ports);
  const output = options.json === true
    ? `${JSON.stringify(report, null, 2)}\n`
    : formatDoctorReport(report, { home });
  if (ports.stdout?.write) ports.stdout.write(output);
  return { exitCode: report.exit_code, report, output };
}
