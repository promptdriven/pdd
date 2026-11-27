// Prompt: prompts/cli/pdd-cli.prompt.md
import { spawnSync } from 'node:child_process';
import { accessSync, constants, existsSync, lstatSync, readdirSync, readFileSync, realpathSync, statSync } from 'node:fs';
import { homedir } from 'node:os';
import { basename, delimiter, dirname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { CommandInputError, parseArgv } from './argument-parser.mjs';
import { NAMES, PUBLIC_COMMAND_MANIFEST, PUBLIC_COMMAND_ROUTES, PUBLIC_HELP_TEXT } from './command-catalog.mjs';
import { gitContext as defaultGitContext, gitFiles } from './shared/git-context.mjs';
import { PACKAGE_ROOT } from './shared/package-root.mjs';
import { causeText } from './shared/safe-read.mjs';
import { resolvePddStateBase } from './shared/state-dir.mjs';

async function maybeCheckReleaseNotice(releaseNotice, input, ports) {
  if (releaseNotice) return releaseNotice(input, ports);
  const resolvedHome = input.env?.HOME || homedir();
  const stateDir = ports?.stateHome
    ? join(ports.stateHome, 'pdd')
    : resolvePddStateBase(resolvedHome ? { ...input.env, HOME: resolvedHome } : input.env);
  if (!input.interactive && !ports?.fetchLatestRelease && !(stateDir && existsSync(join(stateDir, 'release-check.json')))) return null;
  const { checkReleaseNotice } = await import('./release-notice.mjs');
  return checkReleaseNotice(input, ports);
}

function hasExecutableOnPath(name, env) {
  return (env?.PATH ?? '').split(delimiter).filter(Boolean).some(dir => {
    try { accessSync(join(dir, name), constants.X_OK); return true; } catch { return false; }
  });
}

function hasGhHostsConfig(env) {
  const configDir = (env?.GH_CONFIG_DIR && env.GH_CONFIG_DIR.trim())
    || (env?.XDG_CONFIG_HOME && env.XDG_CONFIG_HOME.trim()
      ? join(env.XDG_CONFIG_HOME.trim(), 'gh')
      : join(env?.HOME || homedir(), '.config', 'gh'));
  try { return existsSync(join(configDir, 'hosts.yml')); } catch { return false; }
}

function checkPddAccountNonBlocking(env) {
  if (!hasExecutableOnPath('gh', env)) return { checked: false, connected: false };
  if ((env?.GH_TOKEN && env.GH_TOKEN.trim()) || (env?.GITHUB_TOKEN && env.GITHUB_TOKEN.trim())) {
    return { checked: true, connected: true };
  }
  // Avoid spawning `gh` when unconfigured, because `gh` creates `$HOME/.local/state/gh` on startup.
  if (!hasGhHostsConfig(env)) return { checked: false, connected: false };
  try {
    const res = spawnSync('gh', ['auth', 'token'], { env, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'], timeout: 1500 });
    return { checked: true, connected: !res.error && res.status === 0 && Boolean(res.stdout?.trim()) };
  } catch {
    return { checked: true, connected: false };
  }
}
const defaultReadPackageVersion = ({ packageRoot }) => {
  try { const { version } = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8'));
    return typeof version === 'string' && !!version ? { ok: true, version } : { ok: false, version: '' }; }
  catch { return { ok: false, version: '' }; }
};
function findInvertedNativeOnlyStory(runtime, cwd, words, options) {
  if (['--local', '--files', '--explain-bindings', '--read', '--retry', '--retry-unresolved', '--reconcile', '--reconcile-stale', '--request', '--screen', '--emit-v1', '--write', '--bind-criteria'].some(flag => options[flag])) return null;
  try {
    const root = resolveLintRoot(cwd);
    const found = runtime.findTests({ root });
    let realRoot = root;
    let realCwd = cwd;
    try { realRoot = realpathSync(root); realCwd = realpathSync(cwd); } catch {}
    const normalized = words.map(word => {
      if (typeof word !== 'string' || !word) return word;
      const abs = resolve(realCwd, word);
      const rel = relative(realRoot, abs).split(sep).join('/');
      const inside = rel !== '..' && !rel.startsWith('../');
      let isDir = false;
      try { isDir = inside && statSync(abs).isDirectory(); } catch {}
      return inside && (found.visible?.has(rel) || isDir) ? (rel || '.') : word;
    });
    const { selected, unknown } = runtime.selectTests(found, normalized, options);
    if (unknown?.length || !selected?.length) return null;
    const { rows } = runtime.preflight({ root, found, selected, allowMissingInterfaces: true });
    for (const row of rows) {
      if (row.native_only?.length) {
        const nativePaths = new Set(row.native_only.map(item => item.path));
        const entryPath = (row.steps ?? []).map(s => s?.entry_path).find(e => typeof e === 'string' && !nativePaths.has(e));
        if (entryPath) return { test: row.test, story: row.story, entry_path: entryPath, native_only_path: row.native_only[0].path };
      }
      const isNative = p => p?.interface?.kind === 'native-only' || (p?.frontmatter ?? (typeof p?.text === 'string' ? runtime.parsePromptFrontmatter?.(p.text)?.frontmatter : null))?.kind === 'native-only';
      const entryPaths = [...new Set((row.steps ?? []).map(s => s?.entry_path).filter(p => typeof p === 'string' && p.endsWith('.prompt.md')))];
      for (const entryPath of entryPaths) {
        if (!found.visible?.has(entryPath)) continue;
        let entryPrompt;
        try { entryPrompt = runtime.readPrompt(root, found.visible, entryPath, found.workspace); } catch { continue; }
        if (isNative(entryPrompt)) continue;
        const visited = new Set([entryPath]), queue = [];
        const enqueue = (p, from) => {
          for (const c of Array.isArray(p?.interface?.calls) ? p.interface.calls : []) if (typeof c?.target === 'string' && !visited.has(c.target)) queue.push(c.target);
          if (typeof p?.text === 'string' && typeof runtime.promptMarkdownTargets === 'function')
            for (const t of runtime.promptMarkdownTargets(p.text, from, found.visible)) if (typeof t === 'string' && !visited.has(t)) queue.push(t);
        };
        enqueue(entryPrompt, entryPath);
        while (queue.length > 0 && visited.size < 64) {
          const depPath = queue.shift();
          if (visited.has(depPath) || !found.visible?.has(depPath)) continue;
          visited.add(depPath);
          let depPrompt;
          try { depPrompt = runtime.readPrompt(root, found.visible, depPath, found.workspace); } catch { continue; }
          if (isNative(depPrompt)) return { test: row.test, story: row.story, entry_path: entryPath, native_only_path: depPath };
          enqueue(depPrompt, depPath);
        }
      }
    }
  } catch {}
  return null;
}
const line = (stream, text) => stream.write(`${text}\n`);
// The real reason of an unexpected error, after the fixed safe line.
const reason = error => { const text = causeText(error?.message ?? error); return text ? ` Reason: ${text}` : ''; };
// Stdin as text: a string from tests, else the whole stream.
const readText = async input => {
  if (typeof input === 'string') return input;
  if (!input?.[Symbol.asyncIterator]) return '';
  const chunks = []; for await (const chunk of input) chunks.push(Buffer.from(chunk));
  return Buffer.concat(chunks).toString('utf8');
};
// Autopilot workers start from the default branch on GitHub, so a setting saved only in this checkout never reaches them.
async function autopilotGithub(module, name, input, ports, fallback = '') {
  try { return (await (module ?? await import('./autopilot-github.mjs'))[name](input, ports))?.message || ''; }
  catch { return fallback; }
}
const skillCount = folders => `${folders.length} PDD skill${folders.length === 1 ? '' : 's'}`;
const skillNames = folders => folders.map(folder => basename(folder)).join(', ');
const formatRetiredNames = folders => {
  const names = folders.map(folder => basename(folder));
  if (names.length <= 3) return names.join(', ');
  return `${names.slice(0, 2).join(', ')}, +${names.length - 2} more (${names.length} total)`;
};
const displayPath = (filePath, home) => {
  if (!home || !filePath) return filePath;
  const normHome = resolve(home).replace(/[\\/]+$/, '');
  if (!normHome) return filePath;
  const normFile = resolve(filePath);
  if (normFile === normHome) return '~';
  if (normFile.startsWith(`${normHome}/`) || normFile.startsWith(`${normHome}\\`)) {
    return `~${normFile.slice(normHome.length)}`;
  }
  return filePath;
};
const canonicalFolder = folder => { try { return realpathSync(folder); } catch { return folder; } };
const isProjectFolder = (folder, scope, cwd, home) => {
  if (scope === 'project') return true;
  if (scope === 'user') return false;
  if (home && canonicalFolder(cwd) === canonicalFolder(home)) return false;
  return [join(cwd, '.agents/skills'), join(cwd, '.codex/skills'), join(cwd, '.claude/skills')].includes(folder);
};
// npx skills update changes only what npx skills add recorded (0.1.8 tester); add replaces any copy.
const staleLine = ({ found, scope, stale, staleSkills = [] }, version, cwd, home) => {
  const details = staleSkills.map(({ name, version, state }) => state === 'older'
    ? `${name} is ${version ?? 'unknown'}` : `${name} differs (version ${version ?? 'unknown'})`).join(', ');
  return `PDD skills in ${found} ${stale === 'older' ? `are older than pdd ${version}` : `differ from the skills of pdd ${version}`}.${details ? ` ${details}.` : ''} For copies installed by pdd in user folders, run: pdd setup. For other copies, run: npx skills add promptdriven/pdd${isProjectFolder(found, scope, cwd, home) ? '' : ' -g'} -a codex -a claude-code -y`;
};
const retiredLine = ({ root, found, scope, retiredSkills = [] }, version, cwd, home) => {
  const folder = found ?? root;
  const names = retiredSkills.map(({ name, version: v }) => (v ? `${name} (${v})` : name)).join(', ');
  const action = isProjectFolder(folder, scope, cwd, home)
    ? `Remove these retired PDD skill folders from ${folder} and run: npx skills add promptdriven/pdd -a codex -a claude-code -y`
    : 'Run: pdd setup';
  return `Retired PDD skills remain in ${folder} (pdd ${version} ships only pdd): ${names}. ${action}`;
};
const packageLines = packageRoot => PUBLIC_HELP_TEXT.learnLines.map(line => line.replace('PACKAGE_ROOT', () => packageRoot));
const renderTopic = (topic, packageRoot) => [PUBLIC_HELP_TEXT.heading, '', ...PUBLIC_HELP_TEXT.promptingLines, '', ...packageLines(packageRoot).slice(1)].join('\n');
function tokenizeHelpForm(form) {
  const units = [];
  let cur = '';
  let depth = 0;
  for (const ch of String(form ?? '').trim()) {
    if (ch === '[') { depth += 1; cur += ch; continue; }
    if (ch === ']') { depth = Math.max(0, depth - 1); cur += ch; continue; }
    if (/\s/.test(ch) && depth === 0) {
      if (cur) { units.push(cur); cur = ''; }
      continue;
    }
    cur += ch;
  }
  if (cur) units.push(cur);
  return units;
}
function wrapHelpForm(form, width = 80) {
  const firstIndent = '  ';
  const contIndent = '      ';
  const lines = [];
  let line = '';
  const flush = () => {
    if (!line) return;
    lines.push(`${lines.length === 0 ? firstIndent : contIndent}${line}`);
    line = '';
  };
  for (const unit of tokenizeHelpForm(form)) {
    const indent = lines.length === 0 ? firstIndent : contIndent;
    const maxBody = width - indent.length;
    if (!line && unit.length <= maxBody) { line = unit; continue; }
    if (line && line.length + 1 + unit.length <= maxBody) { line += ` ${unit}`; continue; }
    flush();
    const nextMax = width - contIndent.length;
    if (unit.length <= nextMax || !unit.includes('|')) {
      line = unit;
      continue;
    }
    // Wrap overlong pipe-delimited enums cleanly at `|` boundaries within 80 columns.
    const parts = unit.split('|');
    let chunk = '';
    for (let i = 0; i < parts.length; i += 1) {
      const sep = i < parts.length - 1 ? '|' : '';
      const seg = `${parts[i]}${sep}`;
      if (!chunk) { chunk = seg; continue; }
      if (chunk.length + seg.length <= nextMax) chunk += seg;
      else { lines.push(`${lines.length === 0 ? firstIndent : contIndent}${chunk}`); chunk = seg; }
    }
    line = chunk;
  }
  flush();
  return lines;
}
function wrapHelpDescription(text, width = 76, indent = '    ') {
  const out = [];
  for (const rawLine of String(text ?? '').split('\n')) {
    if (!rawLine.trim()) { out.push(''); continue; }
    // Preserve short code/heredoc lines verbatim without re-wrapping.
    if (/^(?:pdd\s|<)/.test(rawLine)) { out.push(`${indent}${rawLine}`); continue; }
    let line = '';
    for (const word of rawLine.trim().split(/\s+/)) {
      if (!line) { line = word; continue; }
      if (line.length + 1 + word.length <= width) line += ` ${word}`;
      else { out.push(`${indent}${line}`); line = word; }
    }
    if (line) out.push(`${indent}${line}`);
  }
  return out;
}
export function renderHelp(prefix = [], packageRoot = PACKAGE_ROOT) {
  if (prefix.length > 0) {
    const rows = prefix.length === 1 && prefix[0] === '.'
      ? (PUBLIC_COMMAND_ROUTES.find(route => route.id === 'try')?.forms ?? [])
      : PUBLIC_COMMAND_MANIFEST.filter(({ form }) =>
          prefix.every((word, index) => form.slice(4).split(/\s+/)[index] === word));
    const blocks = rows.flatMap(({ form, description }, index) => [
      ...(index ? [''] : []),
      ...wrapHelpForm(form, 80),
      ...wrapHelpDescription(description, 76, '    '),
    ]);
    return [PUBLIC_HELP_TEXT.heading, '', ...blocks].join('\n');
  }
  return [
    PUBLIC_HELP_TEXT.heading, '',
    PUBLIC_HELP_TEXT.usageLine, '',
    'Quick start:', ...PUBLIC_HELP_TEXT.quickStartLines, '',
    ...PUBLIC_HELP_TEXT.groups.flatMap((group, index) => [...(index ? [''] : []), `${group.title}:`, ...group.lines]), '',
    ...PUBLIC_HELP_TEXT.focusedHelpLines,
    ...packageLines(packageRoot), '',
    ...PUBLIC_HELP_TEXT.closingLines,
  ].join('\n');
}
const LINT_FORBIDDEN_TEST_FLAGS = [
  '--live-local', '--command-manifest', '--allow-live-writes',
  '--affected', '--journeys', '--lf', '--cache-clear', '--fresh', '--read', '--retry', '--retry-unresolved',
  '--reconcile', '--reconcile-stale', '--batch-timeout', '--explain-bindings', '--files', '--screen', '--drawing', '--look',
  '--target', '--max-total-calls', '--no-restart-replacement', '--app-map', '--request',
];
const LIVE_LOCAL_INCOMPATIBLE_TEST_FLAGS = [
  '--lint', '--codex', '--local', '--remote', '--target',
  '--read', '--retry', '--retry-unresolved', '--reconcile', '--reconcile-stale', '--files', '--explain-bindings', '--app-map',
  '--screen', '--drawing', '--look', '--emit-v1', '--write', '--bind-criteria',
  '--affected', '--journeys', '--lf', '--cache-clear', '--diff', '--base', '--issue', '--request',
];
const LIVE_LOCAL_INCOMPATIBLE_TRY_FLAGS = [
  '--product', '--parts', '--journey', '--stop', '--save-last', '--no-wait', '--agent',
  '--cli', '--shell', '--serve', '--data', '--show-data', '--quiet', '-q',
];
const isStandaloneProgramTarget = word =>
  typeof word === 'string' && (/\.prompt\.md$/i.test(word) || basename(word).toLowerCase() === 'app-map.json');
const NON_SCENARIO_TEST_DIRS = new Set([
  'fixtures', '__fixtures__', 'mocks', '__mocks__', 'snapshots', '__snapshots__',
  'data', 'testdata', 'golden', 'cassettes',
]);
const NON_SCENARIO_JSON_NAME_RE =
  /^(?:\..+|cases|.*-cases|tsconfig(?:\.[^/]+)?|jsconfig|package(?:-lock)?|npm-shrinkwrap|composer|biome|deno|jsr|eslint|prettier|vitest|jest|babel|firebase|firestore\.indexes|vercel|netlify|wrangler)\.json$/i;
function isRuntimeScenarioJsonPath(rel) {
  if (!rel.endsWith('.json')) return false;
  const parts = rel.split('/');
  const file = parts.at(-1);
  const dirs = parts.slice(0, -1);
  let lastTestDir = -1;
  for (let i = dirs.length - 1; i >= 0; i -= 1) {
    if (dirs[i] === 'test' || dirs[i] === 'tests') { lastTestDir = i; break; }
  }
  if (lastTestDir < 0) return false;
  if (dirs.slice(lastTestDir + 1).some(part => NON_SCENARIO_TEST_DIRS.has(part.toLowerCase()))) return false;
  return !NON_SCENARIO_JSON_NAME_RE.test(file);
}
const NATIVE_STORY_MARKER_RE = /^(?:##\s+Native\s+validation\b|kind:\s*native\b)/im;
const SKIP_SKILL_SYNC_ROUTES = new Set([
  'help', 'version', 'version-detailed', 'completion',
  'autopilot-alerts', 'autopilot-alert',
  'project-files', 'file-owner', 'status', 'init', 'lint', 'prove', 'update-sync', 'vector-export',
  'mcp', 'setup', 'doctor', 'upgrade', 'autopilot-logs',
]);

function resolveLintRoot(cwd) {
  try {
    const out = spawnSync('git', ['rev-parse', '--show-toplevel'], { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'], timeout: 5000 });
    if (out.status === 0 && out.stdout?.trim()) return out.stdout.trim();
  } catch {}
  return cwd;
}

async function collectProjectLintErrors(runtime, root, cwd, words, options) {
  try {
    const { lintRepoProject, resolveLintScope } = await import('./repo-hygiene-lint.mjs');
    if (!words.length) return lintRepoProject({ root }).errors;
    const files = gitFiles(root);
    const scope = resolveLintScope({ root, cwd, files, words });
    if (scope.unmatched.length === 0) {
      if (scope.scenarios.size > 0) {
        try {
          const found = runtime.findTests({ root });
          const { selected, unknown } = runtime.selectTests(found, [...scope.scenarios], options);
          if (!unknown?.length && selected?.length) {
            const { rows } = runtime.preflight({ root, found, selected, allowMissingInterfaces: true });
            for (const row of rows) {
              for (const step of row.steps ?? []) if (typeof step?.entry_path === 'string') scope.prompts.add(step.entry_path);
              for (const p of row.prompts ?? []) if (typeof p === 'string') scope.prompts.add(p);
            }
          }
        } catch {}
      }
      return lintRepoProject({ root, files: scope.effectiveFiles, scope }).errors;
    }
    const found = runtime.findTests({ root });
    const { selected, unknown } = runtime.selectTests(found, words, options);
    if (unknown?.length || !selected?.length) return [];
    const { rows } = runtime.preflight({ root, found, selected, allowMissingInterfaces: true });
    const promptSet = new Set();
    for (const row of rows) {
      for (const step of row.steps ?? []) if (typeof step?.entry_path === 'string') promptSet.add(step.entry_path);
      for (const p of row.prompts ?? []) if (typeof p === 'string') promptSet.add(p);
    }
    return lintRepoProject({ root, promptPaths: [...promptSet], tests: selected }).errors;
  } catch { return []; }
}

function inspectLocalLintRepoFeatures(cwd) {
  let hasNativeStory = false;
  let hasScenarioJson = false;
  const root = resolveLintRoot(cwd);
  let files = [];
  try { files = gitFiles(root); } catch { files = []; }
  for (const rel of files) {
    if (!hasScenarioJson && isRuntimeScenarioJsonPath(rel)) hasScenarioJson = true;
    if (!hasNativeStory && /^(?:user_stories|stories)\/.*\.md$/i.test(rel)) {
      try {
        const text = readFileSync(join(root, rel), 'utf8');
        if (NATIVE_STORY_MARKER_RE.test(text)) hasNativeStory = true;
      } catch {}
    }
    if (hasNativeStory && hasScenarioJson) break;
  }
  return { hasNativeStory, hasScenarioJson, root, files };
}

async function shouldUseRuntimeLocalLint(repoFeatures, cwd, operands) {
  if (!repoFeatures.hasScenarioJson) return false;
  if (!operands.length) return true;
  const hasEmptyOrDirOperand = operands.some(raw => {
    const t = String(raw ?? '').trim();
    if (!t) return true;
    if (t === '.' || t === './' || t.endsWith('/')) return true;
    try { return statSync(resolve(cwd, t)).isDirectory(); } catch { return false; }
  });
  if (hasEmptyOrDirOperand) return false;
  try {
    let realRoot = repoFeatures.root;
    let realCwd = cwd;
    try { realRoot = realpathSync(repoFeatures.root); } catch {}
    try { realCwd = realpathSync(cwd); } catch {}
    const visibleSet = new Set(repoFeatures.files);
    const normalized = operands.map(raw => {
      const word = String(raw ?? '').trim();
      const cand = relative(realRoot, resolve(realCwd, word)).split(sep).join('/');
      return visibleSet.has(cand) ? cand : word;
    });
    if (normalized.every(word => word.endsWith('.prompt.md') && visibleSet.has(word))) {
      return true;
    }
    const runtime = await import('./runtime-seam.mjs');
    const found = runtime.findTests({ root: repoFeatures.root, files: repoFeatures.files, excludeFixtureProjects: false });
    const selection = runtime.selectTests(found, normalized, { native: true });
    return !selection?.unknown?.length
      && !selection?.untested?.length
      && ((selection?.selected?.length ?? 0) > 0 || (selection?.nativeSelections?.length ?? 0) > 0);
  } catch {
    return false;
  }
}

const SKIP_DIRECT_WALK_DIRS = new Set(['.git', 'node_modules', 'dist', 'build', 'coverage', '.next', '.cache', 'vendor', '.pdd']);

function findLocalProjectRoot(cwd) {
  if (typeof cwd !== 'string' || !cwd) return null;
  let dir = resolve(cwd);
  for (let depth = 0; depth < 32; depth += 1) {
    try { if (existsSync(join(dir, '.git'))) return dir; } catch { break; }
    const parent = dirname(dir);
    if (parent === dir) break;
    dir = parent;
  }
  const base = resolve(cwd);
  try {
    if (['user_stories', 'tests', 'test', 'prompts'].some(sub => existsSync(join(base, sub)))) return base;
  } catch {}
  return null;
}

function walkProjectRelFiles(root, startDir, { maxDepth = 6, maxEntries = 2000, skipTestFixtureDirs = false, suffix = '' } = {}) {
  const absStart = join(root, startDir);
  try { if (!lstatSync(absStart).isDirectory()) return []; } catch { return []; }
  const out = [];
  const visit = (relDir, depth) => {
    if (depth > maxDepth || out.length >= maxEntries) return;
    let entries;
    try { entries = readdirSync(join(root, relDir), { withFileTypes: true }); } catch { return; }
    entries.sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
    for (const entry of entries) {
      if (out.length >= maxEntries) break;
      if (entry.isSymbolicLink()) continue;
      const rel = `${relDir}/${entry.name}`;
      if (entry.isDirectory()) {
        if (!SKIP_DIRECT_WALK_DIRS.has(entry.name) && (!skipTestFixtureDirs || !NON_SCENARIO_TEST_DIRS.has(entry.name.toLowerCase()))) {
          visit(rel, depth + 1);
        }
      } else if (entry.isFile() && (!suffix || entry.name.endsWith(suffix))) {
        out.push(rel);
      }
    }
  };
  visit(startDir, 0);
  return out;
}

function resolveLocalDirectTarget(word, cwd) {
  if (typeof word !== 'string' || !word || !word.trim() || word.startsWith('-') || /[\x00-\x1f\x7f]/.test(word)) return null;
  const root = findLocalProjectRoot(cwd);
  if (!root) return null;
  const clean = word.replaceAll('\\', '/').replace(/^\.\//, '');
  if (clean.includes('/') || clean.endsWith('.md') || clean.endsWith('.json')) {
    const candidates = [resolve(cwd, word)];
    const fromRoot = resolve(root, clean);
    if (fromRoot !== candidates[0]) candidates.push(fromRoot);
    let realRoot;
    try { realRoot = realpathSync(root); } catch { return null; }
    for (const candidate of candidates) {
      const rel = relative(root, candidate).split(sep).join('/');
      if (!rel || rel === '..' || rel.startsWith('../')) continue;
      let realCandidate;
      try {
        realCandidate = realpathSync(candidate);
        const realRel = relative(realRoot, realCandidate).split(sep).join('/');
        if (!realRel || realRel === '..' || realRel.startsWith('../') || !statSync(realCandidate).isFile()) continue;
      } catch { continue; }
      const parts = rel.split('/');
      const base = parts.at(-1);
      const operand = candidate === candidates[0] ? word : rel;
      if (rel.endsWith('.md') && parts.slice(0, -1).includes('user_stories') && !/^(?:plan|readme)\.md$/i.test(base)) {
        return { kind: 'story', operand };
      }
      const testDirIdx = parts.slice(0, -1).findIndex(p => p === 'test' || p === 'tests');
      if (rel.endsWith('.json') && testDirIdx >= 0 && !NON_SCENARIO_JSON_NAME_RE.test(base)
        && !parts.slice(testDirIdx + 1, -1).some(p => NON_SCENARIO_TEST_DIRS.has(p.toLowerCase()))) {
        return { kind: 'story', operand };
      }
    }
    return null;
  }
  const storyFiles = walkProjectRelFiles(root, 'user_stories', { suffix: '.md' });
  if (storyFiles.some(rel => !/^(?:plan|readme)\.md$/i.test(basename(rel)) && basename(rel, '.md') === clean)) {
    return { kind: 'story', operand: word };
  }
  for (const testDir of ['tests', 'test']) {
    const testFiles = walkProjectRelFiles(root, testDir, { skipTestFixtureDirs: true, suffix: '.json' });
    if (testFiles.some(rel => !NON_SCENARIO_JSON_NAME_RE.test(basename(rel)) && basename(rel, '.json') === clean)) {
      return { kind: 'story', operand: word };
    }
  }
  const promptFiles = walkProjectRelFiles(root, 'prompts', { suffix: '.prompt.md' });
  const matchingPrompts = promptFiles.filter(rel => basename(rel, '.prompt.md') === clean);
  if (matchingPrompts.length === 1) {
    const operand = relative(resolve(cwd), join(root, matchingPrompts[0])).split(sep).join('/');
    return { kind: 'prompt', operand };
  }
  return null;
}

export async function runPdd(argv, { stdout = process.stdout, stderr = process.stderr,
  cwd = process.cwd(), packageRoot = PACKAGE_ROOT, env = process.env, workflowRunner, workflowAreas,
  stdin = process.stdin, confirm, mcpServer, runtimeSlots, contracts, product, productPorts, gitContext, workflowProve, provePorts,
  autopilotRegressions, autopilotRegressionsPorts = {}, autopilotInvestigate, autopilotInvestigatePorts = {}, issueGraph, issueGraphPorts = {}, autopilotLauncher, autopilotLauncherPorts = {}, workflowAgents, workflowAgentPorts = {}, setupSkills,
  setupProject, initProject, projectStatus, localLint, localLintPorts = {}, proveRunner, proveRunnerPorts = {}, setupAgentMcp, autopilot, autopilotPorts = {}, autopilotLogs, autopilotLogsPorts = {}, autopilotAlerts, autopilotAlertsPorts = {}, autopilotGithub: autopilotGithubModule, autopilotGithubPorts = {}, pathDiagnostic,
  readPackageVersion = defaultReadPackageVersion, findSkills, syncOwnedUserSkills, interpreterVersion, interpreterVersionPorts = {}, releaseNotice, releaseNoticePorts = {}, accountsCli, accountsPorts = {}, cliUpgrade, cliUpgradePorts = {}, doctor, doctorPorts = {}, hostInstallWarnings, codexLint, codexLintPorts = {}, aiLint, aiLintPorts = {}, runtimeCheckReconcile, runtimeCheckReconcilePorts = {} } = {}) {
  let plan;
  try { plan = parseArgv(argv, { resolveTarget: word => resolveLocalDirectTarget(word, cwd) }); }
  catch (error) {
    line(stderr, error instanceof CommandInputError ? error.message : 'The command could not be parsed. Run pdd --help.');
    return 2;
  }
  if ((plan.local === 'version') || (plan.local === 'setup' && plan.options['--upgrade'] !== true)) {
    try {
      const diagFn = pathDiagnostic ?? (await import('./path-diagnostic.mjs')).pathDiagnostic;
      for (const message of diagFn({ packageRoot, cwd, env, mode: plan.local })) line(stderr, message);
    } catch { /* An optional PATH diagnostic never prevents the requested command. */ }
  }
  const code = await (async () => { switch (plan.local) {
    case 'issue-dependency-graph': {
      try { const module = issueGraph ?? await import('./issue-dependency-graph.mjs');
        const result = await module.runIssueGraph({cwd, repository:plan.options['--repo'], issue:plan.options['--issue'], open:!!plan.options['--open']}, issueGraphPorts);
        (result.exitCode ? stderr : stdout).write(result.message); return result.exitCode;
      } catch (error) { line(stderr, `Graph failed.${reason(error)}`); return 1; }
    }
    case 'autopilot-regressions': {
      try {
        const module = autopilotRegressions ?? await import('./autopilot-regressions.mjs');
        const result = await module.runAutopilotRegressions({ cwd, env, json: plan.options['--json'] === true, file: plan.options['--file'] }, autopilotRegressionsPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string' || !result.message.trim()) throw Error();
        line(result.exitCode === 0 ? stdout : stderr, result.message); return result.exitCode;
      } catch { line(stderr, 'Regression scan failed.'); return 1; }
    }
    case 'autopilot-investigate': {
      try {
        const module = autopilotInvestigate ?? await import('./autopilot-core.mjs');
        const result = await module.runAutopilotInvestigate({
          cwd,
          env,
          date: plan.options['--date'] ?? null,
          json: plan.options['--json'] === true,
          writeIssues: plan.options['--write-issues'] === true,
          ...(plan.options['--max-issues'] !== undefined ? { maxIssues: Number(plan.options['--max-issues']) } : {}),
        }, autopilotInvestigatePorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string' || !result.message.trim()) throw Error();
        line(result.exitCode === 0 ? stdout : stderr, result.message); return result.exitCode;
      } catch { line(stderr, 'Autopilot investigation failed.'); return 1; }
    }
    case 'autopilot-logs': {
      const parseSelector = raw => {
        const text = String(raw ?? '').trim().replace(/\/$/, '');
        const plain = /^#?([1-9][0-9]*)$/.exec(text);
        if (plain) return { ok: true, issue: Number(plain[1]), repo: null };
        const qualified = /^([A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+)#([1-9][0-9]*)$/.exec(text);
        if (qualified) return { ok: true, issue: Number(qualified[2]), repo: qualified[1] };
        const url = /^https:\/\/github\.com\/([A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+)\/issues\/([1-9][0-9]*)$/.exec(text);
        if (url) return { ok: true, issue: Number(url[2]), repo: url[1] };
        return { ok: false, issue: null, repo: null };
      };
      const follow = Boolean(plan.options['--follow'] || plan.options['-f']);
      const json = plan.options['--json'] === true;
      if (follow && json) { line(stderr, '--json prints one snapshot and cannot be combined with --follow.'); return 2; }
      const posRaw = plan.operands[0], optRaw = plan.options['--issue'];
      const posParsed = posRaw !== undefined ? parseSelector(posRaw) : null;
      const optParsed = optRaw !== undefined ? parseSelector(optRaw) : null;
      if ((posParsed && !posParsed.ok) || (optParsed && !optParsed.ok)) {
        line(stderr, 'Use a valid issue number, #N, owner/repo#N or GitHub issue URL.'); return 2;
      }
      if (posParsed && optParsed && (posParsed.issue !== optParsed.issue
        || (posParsed.repo && optParsed.repo && posParsed.repo.toLowerCase() !== optParsed.repo.toLowerCase()))) {
        line(stderr, 'Pass the issue once: pdd autopilot logs ISSUE or pdd autopilot logs --issue ISSUE.'); return 2;
      }
      const issue = posParsed && optParsed ? (posParsed.repo ? posRaw : optRaw) : (posRaw ?? optRaw);
      if (follow && issue === undefined) {
        line(stderr, 'Select an issue to follow: pdd autopilot logs ISSUE --follow.'); return 2;
      }
      try {
        const input = {
          cwd,
          env,
          ...(issue !== undefined ? { issue } : {}),
          follow,
          ...(plan.options['--lines'] !== undefined ? { lines: Number(plan.options['--lines']) } : {}),
          json,
        };
        const ports = { stdout, stderr, ...autopilotLogsPorts };
        const result = autopilotLogs
          ? await autopilotLogs.runAutopilotLogs(input, ports)
          : await (await (autopilot ?? import('./autopilot.mjs'))).runAutopilotSubcommand('logs', input, ports);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string') throw Error('Invalid Autopilot logs reply');
        if (!result.streamed && result.message) line(result.exitCode === 0 ? stdout : stderr, result.message);
        return result.exitCode;
      } catch (error) { line(stderr, `Autopilot logs failed.${reason(error)}`); return 1; }
    }
    case 'autopilot-suite': {
      const command = plan.options['--command'];
      if (!command?.trim()) { line(stderr, 'Use pdd autopilot suite --command COMMAND [--timeout MIN].'); return 2; }
      try {
        const { runTestSuite } = await import('./test-suite-queue.mjs');
        const timeout = plan.options['--timeout'] !== undefined ? Number(plan.options['--timeout']) : undefined;
        const result = await runTestSuite(
          { cwd, env, command, ...(timeout !== undefined ? { timeout } : {}) },
          { say: text => line(stdout, text) },
        );
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string') throw Error('Invalid suite reply');
        if (result.message) line(result.exitCode === 0 ? stdout : stderr, result.message);
        return result.exitCode;
      } catch (error) { line(stderr, `Autopilot suite failed.${reason(error)}`); return 1; }
    }
    case 'autopilot-doctor': case 'autopilot-check-base': case 'autopilot-start': case 'autopilot-stop': case 'autopilot-status': case 'autopilot-add': case 'autopilot-release': case 'autopilot-report': case 'autopilot-intake': {
      try {
        const module = autopilotLauncher ?? await import('./autopilot-launcher.mjs');
        const result = await module.runAutopilotLauncher({ command: plan.local.slice(10), issues: [...plan.operands], ...(plan.options['--issues'] !== undefined ? { allowedIssues: plan.options['--issues'] } : {}), ...(plan.options['--issue'] !== undefined ? { issue: plan.options['--issue'] } : {}), runs: plan.options['--runs'], checks: plan.options['--checks'], ...(plan.options['--engine'] ? { engine: plan.options['--engine'] } : {}), ...(plan.options['--label'] ? { label: plan.options['--label'] } : {}), ...(plan.options['--mode'] ? { mode: plan.options['--mode'] } : {}), ...(plan.options['--report'] ? { report: plan.options['--report'] } : {}), ...(plan.options['--decisions'] ? { decisions: plan.options['--decisions'] } : {}), ...(plan.options['--intake'] ? { intake: plan.options['--intake'] } : {}), ...(plan.options['--share'] !== undefined ? { share: plan.options['--share'] } : {}), ...(plan.options['--agent'] !== undefined ? { agent: plan.options['--agent'] } : {}), ...(plan.options['--pool'] !== undefined ? { pool: plan.options['--pool'] } : {}), ...(plan.options['--auto-update'] ? { autoUpdate: plan.options['--auto-update'] } : {}), all: plan.options['--all'] === true, ...(plan.options['--json'] === true ? { json: true } : {}), cwd, packageRoot, env }, autopilotLauncherPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid Autopilot reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message);
        if (result.exitCode === 0 && ['autopilot-start', 'autopilot-status'].includes(plan.local) && plan.options['--all'] !== true && plan.options['--json'] !== true) {
          const warning = await autopilotGithub(autopilotGithubModule, 'checkAutopilotSettings', { cwd }, autopilotGithubPorts);
          if (warning) line(stderr, warning);
        }
        return result.exitCode;
      } catch (error) { line(stderr, `The Autopilot command failed.${reason(error)}`); return 1; }
    }
    case 'autopilot-alert': case 'autopilot-alerts': {
      const action = plan.local === 'autopilot-alert' ? 'alert' : plan.operands[0];
      if (action === 'alert' && plan.options['--input'] !== '-') { line(stderr, 'Use pdd autopilot alert --issue N --kind KIND --input - with the alert JSON on stdin.'); return 2; }
      const discordChannel = plan.options['--discord-channel'], tokenCommand = plan.options['--token-command'];
      if (action !== 'set' && (discordChannel !== undefined || tokenCommand !== undefined)) { line(stderr, 'Use --discord-channel and --token-command only with pdd autopilot alerts set.'); return 2; }
      try {
        const module = autopilotAlerts ?? await import('./autopilot-alerts.mjs');
        let text = '';
        // A token command replaces the stdin secret, so stdin is not read for it.
        if (action === 'alert' || action === 'set' && tokenCommand === undefined) {
          if (action === 'set' && stdin?.isTTY) line(stderr, `Paste the ${discordChannel === undefined ? 'webhook URL' : 'bot token'}, press Enter, then press Ctrl-D. pdd never prints it.`);
          text = await readText(stdin);
        }
        const result = await module.runAutopilotAlerts({ action, cwd, env, text, issue: plan.options['--issue'], kind: plan.options['--kind'], update: plan.options['--update'] === true,
          ...(plan.options['--destination'] === undefined ? {} : { destination: plan.options['--destination'] }), ...(discordChannel === undefined ? {} : { discordChannel }), ...(tokenCommand === undefined ? {} : { tokenCommand }) }, autopilotAlertsPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid alert reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message); return result.exitCode;
      } catch { line(stderr, 'The Autopilot alert command failed.'); return 1; }
    }
    case 'metrics': {
      const args = [...(plan.commandId === 'metrics' ? [] : [plan.commandId.split('.')[1]]), ...plan.operands];
      for (const [name, value] of Object.entries(plan.options)) { args.push(name); if (Array.isArray(value)) args.push(...value); else if (value !== true) args.push(value); }
      const { runMetrics } = await import('./metrics-command.mjs');
      return runMetrics({ argv: args, cwd, env, stdout, stderr });
    }
    case 'accounts': {
      try {
        const module = accountsCli ?? await import('./accounts-cli.mjs');
        const result = await module.runAccountsCli({ commandId: plan.commandId, operands: [...plan.operands], options: { ...plan.options }, cwd, env, stdin }, accountsPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string') throw Error('Invalid accounts reply');
        if (result.message) line(result.exitCode === 0 ? stdout : stderr, result.message);
        return result.exitCode;
      } catch (error) { line(stderr, `The accounts command failed.${reason(error)}`); return 1; }
    }
    case 'help': line(stdout, plan.topic ? renderTopic(plan.topic, packageRoot) : renderHelp(plan.helpPrefix, packageRoot));return 0;
    case 'version': case 'version-detailed': {
      let metadata;
      try { metadata = await readPackageVersion({ packageRoot });
        if (!metadata?.ok || typeof metadata.version !== 'string' || !metadata.version) throw Error('version');
      } catch { line(stderr, 'This PDD package has no readable version metadata.');return 1; }
      if (plan.local === 'version-detailed') {
        let result;
        try { const module = interpreterVersion ?? await import('./interpreter-version.mjs');
          result = await module.runDetailedVersion({ version: metadata.version, env }, interpreterVersionPorts);
        } catch { result = { exit_code: 0, stdout: `PDD CLI: ${metadata.version}\nPDD interpreter: unknown\n`, stderr: '' }; }
        stdout.write(result.stdout); stderr.write(result.stderr); return result.exit_code;
      }
      line(stdout, metadata.version);
      try {
        const findFn = findSkills ?? (await import('./skills-install.mjs')).findSkills;
        const versionHome = env.HOME || homedir();
        for (const result of findFn({ packageRoot, cwd, home: versionHome, claudeConfigDir: env.CLAUDE_CONFIG_DIR, ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}) })) {
          if (result.found && (result.stale === 'older' || result.staleSkills?.some(({ state }) => state === 'older'))) line(stderr, staleLine(result, metadata.version, cwd, versionHome));
          if (result.retiredSkills?.length) line(stderr, retiredLine(result, metadata.version, cwd, versionHome));
        }
      } catch { /* The skills check never changes --version. */ }
      try {
        const notice = await maybeCheckReleaseNotice(releaseNotice, { currentVersion: metadata.version, isVersionCommand: true, interactive: Boolean(stderr?.isTTY), env }, releaseNoticePorts);
        if (typeof notice === 'string' && notice.trim()) line(stderr, notice.trim());
      } catch { /* The release notice never changes --version. */ }
      return 0;
    }
    case 'autopilot.off': case 'autopilot.observe': case 'autopilot.auto': case 'autopilot-trust': case 'autopilot-untrust': {
      try {
        const module = autopilot ?? await import('./autopilot.mjs');
        const input = plan.local.startsWith('autopilot.')
          ? { action: 'mode', mode: plan.local.slice(10) }
          : { action: plan.local.slice(10), names: [...plan.operands] };
        const result = await module.runAutopilot(input, { cwd, stdin, stdout, ...autopilotPorts });
        line(result.exitCode === 0 ? stdout : stderr, result.message);
        if (result.exitCode === 0) {
          if (input.action === 'mode') {
            try {
              const launcher = autopilotLauncher ?? await import('./autopilot-launcher.mjs');
              if (typeof launcher.resetAutopilotCircuitBreaker === 'function') {
                await launcher.resetAutopilotCircuitBreaker({ cwd, env, mode: input.mode }, { ...autopilotPorts, ...autopilotLauncherPorts });
              }
            } catch { /* Local breaker reset never blocks pdd.json settings writes. */ }
          }
          const retry = ['pdd', 'autopilot', input.action === 'mode' ? input.mode : input.action, ...(input.names ?? [])].join(' ');
          const next = await autopilotGithub(autopilotGithubModule, 'publishAutopilotSettings', { cwd, action: input.action, mode: input.mode, names: input.names, retry },
            autopilotGithubPorts, `pdd.json on GitHub was not updated. To retry, run ${retry}.`);
          if (next) line(stdout, next);
        }
        return result.exitCode;
      } catch (error) { line(stderr, `Autopilot settings failed.${reason(error)}`); return 1; }
    }
    case 'product-status': case 'product-next': case 'product-start': {
      try {
        const context = await (gitContext ?? defaultGitContext)(cwd, productPorts);
        if (!context?.toplevel) throw Error('No product repository was found.');
        const module = product ?? await import('./product.mjs');
        if (typeof module.runProduct !== 'function') throw Error('Missing product export');
        const result = await module.runProduct({ command: plan.local.slice(8), run: plan.operands[0],
          noRun: plan.options['--no-run'] === true, agent: plan.options['--agent'] ?? 'codex',
          ...(plan.options['--through'] !== undefined ? { through: plan.options['--through'] } : {}),
          ...(plan.options['--base'] !== undefined ? { base: plan.options['--base'] } : {}),
          json: plan.options['--json'] === true, cwd: context.toplevel, packageRoot }, productPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255
          || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid product reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message.replace(/\n$/, ''));
        return result.exitCode;
      } catch (error) { line(stderr, `The product command failed.${reason(error)}`); return 1; }
    }
    case 'mcp': {
      try {
        if (mcpServer) return await (mcpServer.mcp ?? mcpServer.runMcp).call(mcpServer, { cwd, env }, { stdin, stdout, stderr });
        const { mcp } = await import('./runtime-seam.mjs');
        return await mcp({ cwd, env }, { stdin, stdout, stderr });
      } catch (error) { line(stderr, `pdd mcp could not start.${reason(error)}`); return 1; }
    }
    case 'setup': {
      // Laptop-wide setup: non-blocking PDD account hint, global skills sync, optional Prompt Interpreter MCP registration.
      // Never probes coding-agent logins, never edits repositories, and never prompts for Autopilot settings.
      const yes = plan.options['--yes'] === true;
      const upgrade = plan.options['--upgrade'] === true;
      const interactive = Boolean(confirm) || Boolean(stdin?.isTTY && stdout?.isTTY);
      let code = 0;
      if (!upgrade) {
        const account = checkPddAccountNonBlocking(env);
        if (account.connected) line(stdout, 'GitHub CLI (gh) sign-in detected (for promptdriven.ai).');
        else line(stdout, 'GitHub CLI (gh) is not signed in — run `gh auth login` or visit https://promptdriven.ai/login (continuing setup).');
      }
      const setupHome = env.HOME || homedir();
      const reportedStaleRoots = new Set();
      try {
        const skillsMod = setupSkills ? null : await import('./skills-install.mjs');
        const skillsFn = setupSkills ?? skillsMod.setupSkills;
        const skillOpts = {
          packageRoot,
          cwd,
          home: setupHome,
          claudeConfigDir: env.CLAUDE_CONFIG_DIR,
          env,
          ...(!setupSkills && env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}),
          ...(plan.options['--skills-dir'] !== undefined ? { skillsDir: plan.options['--skills-dir'] } : {}),
        };
        const showPath = folder => displayPath(folder, setupHome);
        for (const result of skillsFn(skillOpts)) {
          if (result.removed?.length) line(stdout, `Removed retired PDD skills from ${showPath(result.root)}: ${formatRetiredNames(result.removed)}`);
          if (result.pluginManaged) {
            if (!upgrade) line(stdout, `PDD skills for ${result.agent} are managed by an installed plugin (${showPath(result.found)}). Skipping duplicate copy.`);
            if (result.error) { line(stderr, `pdd setup: the PDD skills could not be cleaned in ${result.root} (${result.error.code ?? result.error.message}).`); code = 1; }
            continue;
          }
          if (result.updated.length) line(stdout, `Updated ${skillCount(result.updated)} in ${showPath(result.root)}: ${skillNames(result.updated)}`);
          if (result.found && result.stale) {
            reportedStaleRoots.add(canonicalFolder(result.found));
            const version = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
            line(stdout, staleLine(result, version, cwd, setupHome));
          } else if (result.found && !upgrade) line(stdout, `PDD skills found in ${showPath(result.found)}`);
          else if (result.installed.length) line(stdout, `Installed ${skillCount(result.installed)} to ${showPath(result.root)}: ${skillNames(result.installed)}`);
          if (result.error) { line(stderr, `pdd setup: the PDD skills could not be installed in ${result.root} (${result.error.code ?? result.error.message}).`); code = 1; }
        }
        if (upgrade && !setupSkills && plan.options['--skills-dir'] === undefined) {
          const findFn = findSkills ?? skillsMod?.findSkills;
          if (typeof findFn === 'function') {
            try {
              const version = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
              const seenExtra = new Set();
              for (const row of findFn({ packageRoot, cwd, home: setupHome, claudeConfigDir: env.CLAUDE_CONFIG_DIR, ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}) })) {
                const folder = row.found ?? row.root;
                if (!folder) continue;
                const key = canonicalFolder(folder);
                if (row.found && (row.stale === 'older' || row.staleSkills?.some(({ state }) => state === 'older')) && !reportedStaleRoots.has(key) && !seenExtra.has(`stale:${key}`)) {
                  seenExtra.add(`stale:${key}`);
                  line(stdout, staleLine(row, version, cwd, setupHome));
                }
                if (row.retiredSkills?.length && !seenExtra.has(`retired:${key}`)) {
                  seenExtra.add(`retired:${key}`);
                  line(stdout, retiredLine(row, version, cwd, setupHome));
                }
              }
            } catch { /* Read-only post-upgrade discovery never fails setup --upgrade. */ }
          }
        }
      } catch (error) { line(stderr, `pdd setup: skills sync failed.${reason(error)}`); code = 1; }
      try {
        const action = setupAgentMcp ?? (await import('./agent-mcp-setup.mjs')).setupAgentMcp;
        if (await action({ env, packageRoot }, { stdin, stdout, stderr, confirm: interactive ? confirm : undefined, interactive, yes, upgradeOnly: upgrade })) code = 1;
      } catch (error) { line(stderr, `pdd setup: MCP registration failed.${reason(error)}`); code = 1; }
      if (!upgrade && (!pathDiagnostic || hostInstallWarnings)) {
        try {
          const warnFn = hostInstallWarnings ?? (await import('./path-diagnostic.mjs')).formatHostInstallWarnings;
          for (const warning of warnFn({ packageRoot, cwd, env })) line(stderr, warning);
        } catch { /* Advisory install warning never fails setup. */ }
      }
      if (code === 0 && !upgrade) line(stdout, 'Done! Use /pdd in Claude Code or $pdd in Codex. Run `pdd init` inside a repo to add the 4-line PDD block.');
      return code;
    }
    case 'doctor': {
      try {
        const mod = doctor ?? await import('./setup/doctor.mjs');
        const result = await mod.runDoctor({ cwd, env, packageRoot, json: plan.options['--json'] === true }, { stdout, stderr, ...doctorPorts });
        return typeof result === 'number' ? result : (Number.isInteger(result?.exitCode) ? result.exitCode : 1);
      } catch (error) { line(stderr, `pdd doctor failed.${reason(error)}`); return 1; }
    }
    case 'init': {
      try {
        if (setupProject && !initProject) {
          const { file, changed } = setupProject({ cwd, packageRoot });
          line(stdout, changed ? `Wrote the PDD block in ${file}.` : `${file} already has this PDD block. No change.`);
          return 0;
        }
        const runInit = initProject ?? (await import('./project-setup.mjs')).initProject;
        const result = await runInit({ cwd, packageRoot });
        line(stdout, result.changed ? `Wrote the PDD block in ${result.file}.` : `${result.file} already has this PDD block. No change.`);
        if (result.language || result.testCommand) {
          const details = [result.language, result.testCommand ? `test: ${result.testCommand}` : null].filter(Boolean).join(' · ');
          line(stdout, `Detected project: ${details}.`);
        }
        line(stdout, 'Next: invoke /pdd (or $pdd) in your coding agent, or run `pdd status`.');
        return 0;
      } catch (error) {
        line(stderr, `pdd init: ${error.message}`);
        return 1;
      }
    }
    case 'status': {
      try {
        const mod = projectStatus ?? await import('./core/status.mjs');
        return await mod.runStatus({
          cwd,
          paths: [...plan.operands],
          changed: plan.options['--changed'] === true,
          json: plan.options['--json'] === true,
        }, { stdout, stderr });
      } catch (error) { line(stderr, `pdd status failed.${reason(error)}`); return 1; }
    }
    case 'upgrade': {
      try {
        const module = cliUpgrade ?? await import('./setup/cli-upgrade.mjs');
        const result = await module.runCliUpgrade({
          env,
          stdout,
          stderr,
          main: plan.options['--main'] === true,
          packageRoot,
          home: env.HOME || homedir(),
          cwd,
        }, cliUpgradePorts);
        if (typeof result === 'number') return result;
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255) throw Error('Invalid upgrade reply');
        if (typeof result.message === 'string' && result.message) line(result.exitCode === 0 ? stdout : stderr, result.message);
        return result.exitCode;
      } catch (error) { line(stderr, `pdd upgrade failed.${reason(error)}`); return 1; }
    }
    case 'runtime-jobs':
      try {
        if (runtimeSlots) return await (runtimeSlots.jobs ?? runtimeSlots.runJobs).call(runtimeSlots, { env }, { stdout, stderr });
        const { jobs } = await import('./runtime-seam.mjs');
        return await jobs({ env }, { stdout, stderr });
      }
      catch (error) { line(stderr, `Local interpreter jobs could not be read.${reason(error)}`); return 5; }
    case 'contracts': case 'contracts-sync':
      try {
        const input = { words: plan.local === 'contracts-sync' ? ['sync'] : [], options: { ...plan.options }, cwd };
        const ports = { env, stdout, stderr };
        if (contracts) return await (contracts.contracts ?? contracts.runContracts).call(contracts, input, ports);
        const { contracts: run } = await import('./runtime-seam.mjs');
        return await run(input, ports);
      } catch (error) { line(stderr, `Local contracts could not be read.${reason(error)}`); return 5; }
    case 'lint': {
      if (LINT_FORBIDDEN_TEST_FLAGS.some(flag => plan.options[flag] !== undefined)) {
        line(stderr, `This mix of options does not work together. Run pdd ${NAMES.lint} --help.`);
        return 2;
      }
      const plumbingCount = (plan.options['--ai-emit-pack'] === true ? 1 : 0)
        + (plan.options['--ai-emit-verify'] !== undefined ? 1 : 0)
        + (plan.options['--ai-apply'] !== undefined ? 1 : 0);
      if (plumbingCount > 1) {
        line(stderr, `Use only one of --ai-emit-pack, --ai-emit-verify, or --ai-apply at a time.`);
        return 2;
      }
      const isAdaptiveAi = plan.options['--ai'] === true || plumbingCount > 0;
      if (plan.options['--provider'] !== undefined && !isAdaptiveAi) {
        line(stderr, `Use --provider only with pdd ${NAMES.lint} --ai [STORY...] [--diff [BASE]] [--provider codex|claude|gemini] [--json] [--timeout MIN].`);
        return 2;
      }
      if (isAdaptiveAi) {
        const allowedAiKeys = new Set(['--lint', '--ai', '--provider', '--model', '--ai-emit-pack', '--ai-emit-verify', '--ai-apply', '--diff', '--base', '--json', '--timeout']);
        if (Object.keys(plan.options).some(key => !allowedAiKeys.has(key))) {
          line(stderr, `pdd ${NAMES.lint} --ai accepts Story or prompt paths, --diff [BASE], --base REF, --provider codex|claude|gemini, --json, and --timeout MIN.`);
          return 2;
        }
        try {
          const module = aiLint ?? await import('./autopilot/ai-lint-engine.mjs');
          const diffOpt = plan.options['--diff'];
          return await module.runAdaptiveAiLint({
            cwd,
            words: [...plan.operands],
            ...(diffOpt !== undefined ? { diff: diffOpt } : {}),
            ...(plan.options['--base'] !== undefined ? { baseRef: plan.options['--base'] } : {}),
            ...(plan.options['--provider'] !== undefined ? { provider: plan.options['--provider'] } : {}),
            ...(plan.options['--model'] !== undefined ? { model: plan.options['--model'] } : {}),
            ...(plan.options['--timeout'] !== undefined ? { timeoutMinutes: Number(plan.options['--timeout']) } : {}),
            json: plan.options['--json'] === true,
            emitPack: plan.options['--ai-emit-pack'] === true,
            ...(plan.options['--ai-emit-verify'] !== undefined ? { emitVerifyPath: plan.options['--ai-emit-verify'] } : {}),
            ...(plan.options['--ai-apply'] !== undefined ? { applyPath: plan.options['--ai-apply'] } : {}),
            env,
          }, { stdout, stderr, stdin, ...aiLintPorts });
        } catch (error) {
          line(stderr, `AI lint incomplete/unavailable.${reason(error)}`);
          return 1;
        }
      }
      if (plan.options['--issue'] !== undefined && plan.options['--codex'] !== true) {
        line(stderr, `Use --issue only with pdd ${NAMES.lint} --codex [STORY...] [--issue N|FILE] [--json] [--timeout MIN].`);
        return 2;
      }
      if (plan.options['--codex'] === true) {
        if (Object.keys(plan.options).some(key => !['--lint', '--codex', '--issue', '--json', '--timeout'].includes(key))) {
          line(stderr, `pdd ${NAMES.lint} --codex accepts only Story or prompt paths, --json, and --timeout MIN, plus optional --issue N|FILE.`); return 2;
        }
        try {
          const module = codexLint ?? await import('./codex-lint.mjs');
          return await module.runCodexLint({
            cwd,
            words: [...plan.operands],
            ...(plan.options['--issue'] !== undefined ? { issue: plan.options['--issue'] } : {}),
            ...(plan.options['--timeout'] !== undefined ? { timeoutMinutes: Number(plan.options['--timeout']) } : {}),
            json: plan.options['--json'] === true,
            env,
          }, { stdout, stderr, ...codexLintPorts });
        } catch (error) {
          line(stderr, `Codex lint failed before completing.${reason(error)}`);
          return 1;
        }
      }
      if (plan.options['--remote'] === true && plan.options['--local'] === true) {
        line(stderr, `Use either --local or --remote with pdd ${NAMES.lint}, not both.`);
        return 2;
      }
      if (plan.options['--max-calls'] !== undefined && plan.options['--remote'] !== true) {
        line(stderr, `Use --max-calls only with pdd ${NAMES.lint} --remote (default pdd ${NAMES.lint} runs offline with 0 AI calls).`);
        return 2;
      }
      if (plan.options['--timeout'] !== undefined && plan.options['--remote'] !== true && plan.options['--codex'] !== true) {
        line(stderr, `Use --timeout only with pdd ${NAMES.lint} --remote or pdd ${NAMES.lint} --codex.`);
        return 2;
      }
      const needsRemoteOrCompiler = Boolean(
        plan.options['--remote'] === true
        || plan.options['--emit-v1'] === true
        || plan.options['--write'] === true
        || plan.options['--bind-criteria'] === true,
      );
      const repoFeatures = (!needsRemoteOrCompiler && !localLint && plan.options['--diff'] === undefined && plan.options['--base'] === undefined)
        ? inspectLocalLintRepoFeatures(cwd)
        : { hasNativeStory: false, hasScenarioJson: false, root: cwd, files: [] };
      const needsRuntimeLocalAssessment = plan.options['--local'] === true
        && await shouldUseRuntimeLocalLint(repoFeatures, cwd, [...plan.operands]);
      if (needsRemoteOrCompiler || needsRuntimeLocalAssessment) {
        try {
          const runtime = await import('./runtime-seam.mjs');
          const { '--remote': _remote, '--diff': _diff, '--base': _base, ...forwardOptions } = plan.options;
          const opts = { ...forwardOptions, '--lint': true };
          const inverted = findInvertedNativeOnlyStory(runtime, cwd, [...plan.operands], opts);
          if (inverted) line(stderr, `Advisory [inverted-native-only-dependency]: Story test ${inverted.test} enters checkable prompt ${inverted.entry_path}, which links kind: native-only prompt ${inverted.native_only_path} under ## Dependencies. Invert the dependency so ${inverted.native_only_path} depends on ${inverted.entry_path} and inject a <port>.<op> port.`);
          const isLintCheckMode = !['--emit-v1', '--write', '--bind-criteria'].some(flag => opts[flag]);
          const lintRoot = isLintCheckMode ? resolveLintRoot(cwd) : null;
          let seamProjectErrors = null;
          const onProjectLintResult = lintRoot && opts['--local'] === true
            ? result => {
                if (!result || !Array.isArray(result.errors)) return;
                if (!seamProjectErrors) seamProjectErrors = [];
                for (const err of result.errors) if (!seamProjectErrors.includes(err)) seamProjectErrors.push(err);
              }
            : undefined;
          if (lintRoot && opts['--json'] === true) {
            let captured = '';
            const bufferedStdout = { write: chunk => { captured += String(chunk); return true; } };
            const runtimeCode = await runtime.lint({ words: [...plan.operands], options: opts, cwd }, { stdout: bufferedStdout, stderr, env, ...(onProjectLintResult ? { onProjectLintResult } : {}) });
            if (runtimeCode === 0 || runtimeCode === 1) {
              const projectErrors = seamProjectErrors ?? await collectProjectLintErrors(runtime, lintRoot, cwd, [...plan.operands], opts);
              if (projectErrors.length > 0 || opts['--local'] === true) {
                try {
                  const parsed = JSON.parse(captured.trim());
                  if (opts['--local'] === true && !parsed.schema_version) parsed.schema_version = 'pdd.local-lint.v1';
                  if (projectErrors.length > 0) {
                    parsed.problems = [...(Array.isArray(parsed.problems) ? parsed.problems : []), ...projectErrors];
                    parsed.ok = false;
                    parsed.exit_code = 1;
                    stdout.write(`${JSON.stringify(parsed)}\n`);
                    return 1;
                  }
                  stdout.write(`${JSON.stringify(parsed)}\n`);
                  return runtimeCode;
                } catch {}
              }
            }
            if (captured) stdout.write(captured);
            return runtimeCode;
          }
          const runtimeCode = await runtime.lint({ words: [...plan.operands], options: opts, cwd }, { stdout, stderr, env, ...(onProjectLintResult ? { onProjectLintResult } : {}) });
          if (lintRoot && (runtimeCode === 0 || runtimeCode === 1)) {
            const projectErrors = seamProjectErrors ?? await collectProjectLintErrors(runtime, lintRoot, cwd, [...plan.operands], opts);
            if (projectErrors.length > 0) {
              for (const errLine of projectErrors) line(stderr, errLine);
              return 1;
            }
          }
          return runtimeCode;
        } catch (error) {
          line(stderr, `pdd stopped with an internal error. If it sent checks, read them with pdd test --read. Do not send them again.${reason(error)}`);
          return 3;
        }
      }
      try {
        const mod = localLint ?? await import('./core/lint/run-local-lint.mjs');
        const diffOpt = plan.options['--diff'];
        return await mod.runLocalLint({
          cwd,
          words: [...plan.operands],
          json: plan.options['--json'] === true,
          ...(diffOpt !== undefined ? { diff: diffOpt } : {}),
          ...(plan.options['--base'] !== undefined ? { baseRef: plan.options['--base'] } : {}),
          env,
        }, { stdout, stderr, ...localLintPorts });
      } catch (error) {
        line(stderr, `Local lint failed.${reason(error)}`);
        return 2;
      }
    }
    case 'vector-export': {
      try {
        const { runVectorExport } = await import('./core/lint/vector-export.mjs');
        return runVectorExport({
          cwd,
          inputPath: plan.operands[0] ?? null,
          outPath: plan.options['--out'] ?? null,
          storyPath: plan.options['--story'] ?? null,
          entryPath: plan.options['--entry'] ?? null,
          op: plan.options['--op'] ?? null,
          criterion: plan.options['--criterion'] ?? null,
          ...(plan.options['--max-steps'] !== undefined ? { maxSteps: Number(plan.options['--max-steps']) } : {}),
          split: plan.options['--split'] === true,
          write: plan.options['--write'] === true,
          json: plan.options['--json'] === true,
        }, { stdout, stderr, stdin });
      } catch (error) {
        line(stderr, `Vector export failed.${reason(error)}`);
        return 2;
      }
    }
    case 'prove': {
      try {
        const mod = proveRunner ?? await import('./core/prove.mjs');
        const res = await mod.runProve({
          cwd,
          ...(plan.options['--base'] !== undefined ? { base: plan.options['--base'] } : {}),
          ...(plan.options['--test'] !== undefined ? { test: plan.options['--test'] } : {}),
          ...(plan.options['--expect'] !== undefined ? { expect: plan.options['--expect'] } : {}),
          ...(plan.options['--overlay'] !== undefined ? { overlay: plan.options['--overlay'] } : {}),
          ...(plan.options['--setup'] !== undefined ? { setup: plan.options['--setup'] } : {}),
          ...(plan.options['--timeout'] !== undefined ? { timeoutMinutes: Number(plan.options['--timeout']) } : {}),
          json: plan.options['--json'] === true,
          env,
        }, { stdout, stderr, ...proveRunnerPorts });
        return typeof res === 'number' ? res : (Number.isInteger(res?.exitCode) ? res.exitCode : 1);
      } catch (error) {
        line(stderr, `pdd prove failed.${reason(error)}`);
        return 2;
      }
    }
    case 'runtime-check':
    case 'runtime-try': {
      const liveLocalEnabled = plan.options['--live-local'];
      if (liveLocalEnabled === undefined || liveLocalEnabled === false) {
        if (plan.options['--command-manifest'] !== undefined || plan.options['--allow-live-writes'] !== undefined) {
          line(stderr, '--command-manifest and --allow-live-writes require --live-local.');
          return 2;
        }
      } else {
        if (
          liveLocalEnabled !== true ||
          typeof plan.options['--command-manifest'] !== 'string' ||
          !plan.options['--command-manifest'].trim() ||
          (plan.options['--allow-live-writes'] !== undefined && typeof plan.options['--allow-live-writes'] !== 'boolean')
        ) {
          line(stderr, '--live-local requires an explicit --command-manifest path and Boolean write flag.');
          return 2;
        }
        const incompatible = plan.local === 'runtime-check'
          ? LIVE_LOCAL_INCOMPATIBLE_TEST_FLAGS
          : LIVE_LOCAL_INCOMPATIBLE_TRY_FLAGS;
        if (incompatible.some(flag => plan.options[flag] !== undefined)) {
          line(
            stderr,
            plan.local === 'runtime-check'
              ? `This option combination is unavailable with --live-local. Run pdd ${NAMES.test} --help.`
              : 'This option combination is unavailable with --live-local. Live Prompt Interpreter sessions must stay in the foreground.',
          );
          return 2;
        }
        if (plan.local === 'runtime-try' && plan.operands.some(isStandaloneProgramTarget)) {
          line(stderr, '--live-local applies to Story runs, not standalone .prompt.md or app-map.json targets.');
          return 2;
        }
      }
      if (plan.local === 'runtime-check' && (plan.options['--ai'] === true || plan.options['--provider'] !== undefined || plan.options['--ai-emit-pack'] === true || plan.options['--ai-emit-verify'] !== undefined || plan.options['--ai-apply'] !== undefined)) {
        line(stderr, `Use pdd ${NAMES.lint} --ai [STORY...] [--diff [BASE]] [--provider codex|claude|gemini] [--json] [--timeout MIN].`);
        return 2;
      }
      if (plan.local === 'runtime-check' && (plan.options['--issue'] !== undefined || plan.options['--codex'] === true)) {
        line(stderr, `Use pdd ${NAMES.lint} --codex [STORY...] [--issue N|FILE] [--json] [--timeout MIN].`);
        return 2;
      }
      if (plan.local === 'runtime-check' && plan.options['--reconcile'] !== undefined) {
        if (plan.operands.length > 0 || Object.keys(plan.options).some(key => !['--reconcile', '--json'].includes(key))) {
          line(stderr, `Use pdd ${NAMES.test} --reconcile REQUEST_ID|BATCH [--json] without other options or Stories.`);
          return 2;
        }
        try {
          const runtime = await import('./runtime-seam.mjs');
          return await runtime.runCheck(
            { words: [...plan.operands], options: { ...plan.options }, cwd },
            {
              env,
              stdout,
              stderr,
              ...runtimeCheckReconcilePorts,
              ...(runtimeCheckReconcile ? { reconcileCheckReceipt: runtimeCheckReconcile } : {}),
            },
          );
        } catch (error) {
          if (error?.code === 'invalid-request-id' || error?.code === 'invalid-batch-id' || error?.exitCode === 2) {
            line(stderr, causeText(error.message) || 'Invalid reconciliation target.');
            return 2;
          }
          if (error?.code === 'reconciliation-unsupported' || error?.exitCode === 5) {
            line(stderr, causeText(error.message) || 'CHECK receipt reconciliation is unavailable.');
            return 5;
          }
          line(stderr, `CHECK receipt reconciliation failed.${reason(error)}`);
          return 3;
        }
      }
      if (plan.local === 'runtime-check' && plan.options['--reconcile-stale'] !== undefined) {
        if (plan.operands.length > 0 || Object.keys(plan.options).some(key => !['--reconcile-stale', '--json'].includes(key))) {
          line(stderr, `Use pdd ${NAMES.test} --reconcile-stale [--json] without other options or Stories.`);
          return 2;
        }
        try {
          const runtime = await import('./runtime-seam.mjs');
          return await runtime.runCheck(
            { words: [...plan.operands], options: { ...plan.options }, cwd },
            {
              env,
              stdout,
              stderr,
              ...runtimeCheckReconcilePorts,
            },
          );
        } catch (error) {
          if (error?.exitCode === 2) {
            line(stderr, causeText(error.message) || 'Invalid --reconcile-stale request.');
            return 2;
          }
          if (error?.exitCode === 5) {
            line(stderr, causeText(error.message) || 'Stale reservation reconciliation is unavailable.');
            return 5;
          }
          line(stderr, `Stale reservation reconciliation failed.${reason(error)}`);
          return 3;
        }
      }
      try {
        if (plan.local === 'runtime-check' && plan.options['--target'] === 'code') {
          if (Object.keys(plan.options).some(key => !['--target', '--json'].includes(key))) { line(stderr, 'pdd test --target code accepts only --json and Story selections.'); return 2; }
          const { runCompiledTest } = await import('./compiled-test.mjs');
          return await runCompiledTest({ root: cwd, words: [...plan.operands], json: !!plan.options['--json'] }, { stdout, stderr });
        }
        const runtime = await import('./runtime-seam.mjs');
        if (plan.local === 'runtime-check') {
          const inverted = findInvertedNativeOnlyStory(runtime, cwd, [...plan.operands], { ...plan.options });
          if (inverted) line(stderr, `Advisory [inverted-native-only-dependency]: Story test ${inverted.test} enters checkable prompt ${inverted.entry_path}, which links kind: native-only prompt ${inverted.native_only_path} under ## Dependencies. Invert the dependency so ${inverted.native_only_path} depends on ${inverted.entry_path} and inject a <port>.<op> port.`);
        }
        const action = plan.local === 'runtime-try' ? 'runTry' : 'check';
        return await runtime[action]({ words: [...plan.operands], options: { ...plan.options }, cwd }, { stdout, stderr, env });
      } catch (error) {
        line(stderr, `pdd stopped with an internal error. If it sent checks, read them with pdd test --read. Do not send them again.${reason(error)}`);
        return 3;
      }
    }
    case 'project-files': {
      const { runProjectFiles } = await import('./project-files.mjs');
      return runProjectFiles({ cwd, json: !!plan.options['--json'] }, { stdout, stderr });
    }
    case 'file-owner': {
      const { runOwner } = await import('./file-owner.mjs');
      return runOwner({ cwd, paths: [...plan.operands], json: !!plan.options['--json'] }, { stdout, stderr });
    }
    case 'update-sync': {
      try {
        const mod = await import('./update-sync.mjs');
        const runUpdate = mod.runUpdateSync ?? mod.runUpdate;
        return runUpdate({
          cwd,
          files: [...plan.operands],
          ...(plan.options['--from'] !== undefined ? { from: plan.options['--from'] } : {}),
          branch: plan.options['--branch'] === true,
          all: plan.options['--all'] === true,
          check: plan.options['--check'] === true,
          write: plan.options['--write'] === true,
          json: plan.options['--json'] === true,
        }, { stdout, stderr });
      } catch (error) { line(stderr, `pdd update failed.${reason(error)}`); return 1; }
    }
    case 'completion': {
      const { renderCompletion } = await import('./completion.mjs');
      stdout.write(renderCompletion(plan.operands[0]));
      return 0;
    }
    default: line(stderr, 'Unsupported command in pdd. Run pdd --help.');return 2;
  } })();
  const quietDirect = plan.local === 'runtime-try' && (plan.options['--quiet'] === true || plan.options['-q'] === true);
  const hasSafeHome = env.HOME === undefined || (typeof env.HOME === 'string' && env.HOME.trim().length > 0 && isAbsolute(env.HOME));
  if (code === 0
    && hasSafeHome
    && !SKIP_SKILL_SYNC_ROUTES.has(plan.local)
    && !quietDirect
    && !(plan.local === 'runtime-check' && plan.options['--files'] === true)
    && !(plan.local === 'accounts' && plan.options['--quiet'] === true)
    && !(plan.local === 'lint' && (plan.options['--ai-emit-pack'] === true || plan.options['--ai-emit-verify'] !== undefined || plan.options['--ai-apply'] !== undefined))
    && plan.options['--json'] !== true
    && !argv.includes('--json')) {
    try {
      const syncFn = syncOwnedUserSkills ?? (await import('./skills-install.mjs')).syncOwnedUserSkills;
      const { updated } = syncFn({
        packageRoot,
        home: env.HOME || homedir(),
        claudeConfigDir: env.CLAUDE_CONFIG_DIR,
        ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}),
        ...(env.PDD_STATE_DIR ? { stateRoot: env.PDD_STATE_DIR } : {}),
        env,
      });
      if (updated?.length > 0 && stderr?.isTTY === true) {
        const metadata = await readPackageVersion({ packageRoot });
        if (metadata?.ok && typeof metadata.version === 'string' && metadata.version)
          line(stderr, `Updated PDD skills to ${metadata.version} (${updated.join(', ')}).`);
      }
    } catch { /* Post-upgrade skill sync never blocks or fails a CLI command. */ }
  }
  if (!['help', 'completion', 'version', 'version-detailed', 'mcp', 'upgrade', 'update-sync', 'project-files', 'setup', 'doctor', 'init', 'status', 'lint', 'prove', 'vector-export'].includes(plan.local) && !quietDirect && !(plan.local === 'runtime-check' && plan.options['--files'] === true) && !(plan.local === 'accounts' && plan.options['--quiet'] === true) && !(plan.local === 'autopilot-logs' && (plan.options['--follow'] === true || plan.options['-f'] === true)) && plan.options['--json'] !== true && (stderr?.isTTY === true || Boolean(releaseNotice))) {
    try {
      const metadata = await readPackageVersion({ packageRoot });
      if (metadata?.ok && typeof metadata.version === 'string' && metadata.version) {
        const notice = await maybeCheckReleaseNotice(releaseNotice, { currentVersion: metadata.version, isVersionCommand: false, interactive: Boolean(stderr?.isTTY), env }, releaseNoticePorts);
        if (typeof notice === 'string' && notice.trim()) line(stderr, notice.trim());
      }
    } catch { /* An optional release notice never changes command output or exit status. */ }
  }
  return code;
}
