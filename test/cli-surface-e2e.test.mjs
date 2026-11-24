import './helpers/test-home.mjs';
import test, { after, describe } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawn } from 'node:child_process';
import http from 'node:http';
import {
  chmodSync,
  cpSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  realpathSync,
  rmSync,
  statSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { PUBLIC_COMMAND_IDS, PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { proseSha256 } from '../src/runtime-seam.mjs';
import { promptHeaderHash } from '../src/file-owner.mjs';
import { configureCheckCapacity } from '../src/test-suite-queue.mjs';

const PACKAGE_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const BIN_ENTRY = join(PACKAGE_ROOT, 'bin', 'pdd.mjs');
const NET_GUARD = join(PACKAGE_ROOT, 'test', 'helpers', 'test-net-guard.mjs');
const PKG_VERSION = JSON.parse(readFileSync(join(PACKAGE_ROOT, 'package.json'), 'utf8')).version;
const GIT_BIN = execFileSync('which', ['git'], { encoding: 'utf8' }).trim() || '/usr/bin/git';

const tempDirs = [];
const activeServers = [];

after(async () => {
  await Promise.all(
    activeServers.map(
      server => new Promise(resolveClose => server.close(() => resolveClose())),
    ),
  );
  for (const dir of tempDirs) {
    rmSync(dir, { recursive: true, force: true });
  }
});

/** Create a tracked temporary directory cleaned up automatically after the file finishes. */
function makeTempDir(prefix) {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), prefix)));
  tempDirs.push(dir);
  return dir;
}

/** Write a file inside root, creating parent directories as needed. */
function writeText(root, relPath, content, options = {}) {
  const full = join(root, relPath);
  mkdirSync(dirname(full), { recursive: true });
  writeFileSync(full, content, options);
  return full;
}

/** Execute git with isolated author/config environment inside a fixture repository. */
function runGit(cwd, args, extraEnv = {}) {
  return execFileSync(GIT_BIN, args, {
    cwd,
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
    env: {
      PATH: `${dirname(GIT_BIN)}:/usr/bin:/bin`,
      HOME: cwd,
      GIT_CONFIG_NOSYSTEM: '1',
      GIT_CONFIG_GLOBAL: '/dev/null',
      GIT_AUTHOR_NAME: 'E2E Fixture',
      GIT_AUTHOR_EMAIL: 'fixture@example.invalid',
      GIT_COMMITTER_NAME: 'E2E Fixture',
      GIT_COMMITTER_EMAIL: 'fixture@example.invalid',
      ...extraEnv,
    },
  }).trim();
}

/** Run async work items with bounded concurrency so subprocess suites stay fast and deterministic. */
async function runPool(items, concurrency, worker) {
  const results = new Array(items.length);
  let cursor = 0;
  const lanes = Array.from({ length: Math.min(concurrency, items.length) }, async () => {
    while (cursor < items.length) {
      const index = cursor++;
      results[index] = await worker(items[index], index);
    }
  });
  await Promise.all(lanes);
  return results;
}

/**
 * Create a self-contained directory of safe executable shims placed first on PATH.
 * Prevents any spawned pdd subprocess from touching real GitHub, Herdr, launchctl/systemd,
 * AI agent binaries, browser launchers, or global npm.
 */
function createShimBin(baseDir) {
  const binDir = join(baseDir, 'shims');
  mkdirSync(binDir, { recursive: true });
  const nodeBin = process.execPath;
  const writeNodeShim = (name, scriptBody) => {
    const scriptPath = join(binDir, `${name}.cjs`);
    writeFileSync(scriptPath, scriptBody, { mode: 0o755 });
    const wrapperPath = join(binDir, name);
    writeFileSync(
      wrapperPath,
      `#!/bin/sh\nexec '${nodeBin.replace(/'/g, "'\\''")}' '${scriptPath.replace(/'/g, "'\\''")}' "$@"\n`,
      { mode: 0o755 },
    );
  };

  // Safe `gh` shim: defaults to offline/unauthenticated unless PDD_E2E_FAKE_GH is set.
  writeNodeShim(
    'gh',
    `
const fs = require('node:fs');
const args = process.argv.slice(2);
const mode = process.env.PDD_E2E_FAKE_GH || 'offline';
const repo = process.env.PDD_E2E_REPO || 'example/cli-fixture';
const out = value => process.stdout.write(typeof value === 'string' ? value : JSON.stringify(value));
if (mode === 'offline') {
  process.stderr.write('gh: not logged into any GitHub hosts (e2e offline shim)\\n');
  process.exit(1);
}
if (args[0] === 'auth' && args[1] === 'token') {
  out('ghu_e2e_synthetic_token_000000\\n');
  process.exit(0);
}
if (args[0] === 'auth' && args[1] === 'status') {
  out('Logged in to github.com as e2e-user\\n');
  process.exit(0);
}
if (args[0] === 'repo' && args[1] === 'view') {
  const jqIndex = args.indexOf('--jq');
  if (jqIndex !== -1 && args[jqIndex + 1] === '.nameWithOwner') {
    out(repo + '\\n');
    process.exit(0);
  }
  out({
    nameWithOwner: repo,
    defaultBranchRef: { name: 'main' },
    url: 'https://github.com/' + repo,
    owner: { login: repo.split('/')[0] },
    viewerPermission: 'ADMIN',
    mergeCommitAllowed: true,
    squashMergeAllowed: true,
    rebaseMergeAllowed: false,
  });
  process.exit(0);
}
if (args[0] === 'issue' && args[1] === 'create') {
  out('https://github.com/' + repo + '/issues/91\\n');
  process.exit(0);
}
if (args[0] === 'pr' && args[1] === 'list') {
  out([]);
  process.exit(0);
}
if (args[0] === 'pr' && args[1] === 'view') {
  out({ number: 55, state: 'OPEN', url: 'https://github.com/' + repo + '/pull/55', baseRefName: 'main', headRefName: 'pdd/issue-42', body: '' });
  process.exit(0);
}
if (args[0] === 'api') {
  const endpoint = args[1] || '';
  if (endpoint === 'user') {
    out({ login: 'e2e-user' });
    process.exit(0);
  }
  if (endpoint === 'graphql') {
    out({ data: {} });
    process.exit(0);
  }
  if (endpoint.includes('/labels')) {
    out({ name: 'pdd:autopilot' });
    process.exit(0);
  }
  if (endpoint.startsWith('search/issues')) {
    out({ items: [], total_count: 0, incomplete_results: false });
    process.exit(0);
  }
  if (/^repos\\/[^/]+\\/[^/]+\\/issues\\/\\d+$/.test(endpoint)) {
    const num = Number(endpoint.split('/').at(-1));
    const payload = {
      number: num,
      title: 'E2E fixture issue #' + num,
      body: 'Synthetic issue body for CLI E2E test.',
      state: 'open',
      html_url: 'https://github.com/' + repo + '/issues/' + num,
      user: { login: 'e2e-user' },
      author_association: 'OWNER',
      labels: [],
      assignees: [],
    };
    if (args.includes('--include')) {
      out('HTTP/2.0 200 OK\\r\\ncontent-type: application/json\\r\\n\\r\\n' + JSON.stringify(payload));
    } else {
      out(payload);
    }
    process.exit(0);
  }
  if (endpoint.endsWith('/issues') || endpoint.includes('/issues?')) {
    out([]);
    process.exit(0);
  }
  if (endpoint.includes('/collaborators')) {
    out([{ login: 'e2e-user', permissions: { admin: true, push: true } }]);
    process.exit(0);
  }
  if (endpoint.includes('/comments') || endpoint.includes('/timeline') || endpoint.includes('/commits') || endpoint.includes('/pulls')) {
    out([]);
    process.exit(0);
  }
  if (endpoint.includes('/contents/pdd.json')) {
    process.stderr.write('gh: Not Found (HTTP 404)\\n');
    process.exit(1);
  }
  out({});
  process.exit(0);
}
process.stderr.write('gh: unsupported synthetic route ' + args.join(' ') + '\\n');
process.exit(1);
`,
  );

  // Safe `codex` shim: supports --version, login status, and synthetic `codex login` for accounts add.
  writeNodeShim(
    'codex',
    `
const fs = require('node:fs');
const path = require('node:path');
const args = process.argv.slice(2);
if (process.env.PDD_E2E_CODEX_LOG) {
  fs.appendFileSync(
    process.env.PDD_E2E_CODEX_LOG,
    JSON.stringify({ args, codexHome: process.env.CODEX_HOME ?? null }) + '\\n',
  );
}
if (args[0] === '--version' || args[0] === '-V') {
  process.stdout.write('codex-cli 0.99.0-e2e\\n');
  process.exit(0);
}
if (args[0] === 'login' && args[1] === 'status') {
  process.stdout.write('Logged in using ChatGPT (e2e-shim)\\n');
  process.exit(0);
}
if (args[0] === 'login') {
  const home = process.env.CODEX_HOME || path.join(process.env.HOME || '.', '.codex');
  fs.mkdirSync(home, { recursive: true });
  const header = Buffer.from(JSON.stringify({ alg: 'none', typ: 'JWT' })).toString('base64url');
  const payload = Buffer.from(JSON.stringify({
    sub: 'auth0|e2e-added',
    email: 'e2e-added@example.invalid',
    exp: Math.floor(Date.now() / 1000) + 7200,
    'https://api.openai.com/auth': { chatgpt_account_id: 'acct_e2e_added', chatgpt_plan_type: 'pro' },
  })).toString('base64url');
  const jwt = header + '.' + payload + '.sig';
  fs.writeFileSync(path.join(home, 'auth.json'), JSON.stringify({
    auth_mode: 'chatgpt',
    tokens: { access_token: jwt, id_token: jwt, refresh_token: 'rt_e2e_added_token', account_id: 'acct_e2e_added' },
    last_refresh: new Date().toISOString(),
  }, null, 2));
  process.stdout.write('Logged in (e2e-shim)\\n');
  process.exit(0);
}
process.stdout.write('codex-e2e-ok ' + args.join(' ') + '\\n');
process.exit(0);
`,
  );

  // Safe `claude`, `gemini`, `agy` shims.
  for (const agent of ['claude', 'gemini', 'agy']) {
    writeNodeShim(
      agent,
      `
const args = process.argv.slice(2);
if (args[0] === '--version') { process.stdout.write('${agent} 1.0.0-e2e\\n'); process.exit(0); }
process.stderr.write('${agent}: not logged in (e2e shim)\\n');
process.exit(1);
`,
    );
  }

  // Safe `launchctl` and `systemctl` shims: never touch macOS LaunchAgents or Linux systemd.
  writeNodeShim(
    'launchctl',
    `
const args = process.argv.slice(2);
if (args[0] === 'print' && /^gui\\/\\d+$/.test(args[1] || '')) {
  process.stdout.write('gui/e2e = {}\\n');
  process.exit(0);
}
if (args[0] === 'print') {
  process.exit(113);
}
process.exit(0);
`,
  );
  writeNodeShim(
    'systemctl',
    `
const args = process.argv.slice(2);
if (args.includes('is-active')) process.exit(3);
process.exit(0);
`,
  );

  // Safe `open`, `xdg-open`, and `npm` no-op shims.
  for (const tool of ['open', 'xdg-open']) {
    writeNodeShim(tool, 'process.exit(0);\n');
  }
  writeNodeShim(
    'npm',
    `process.stderr.write('npm disabled inside CLI E2E sandbox\\n'); process.exit(1);\n`,
  );

  // Transparent `git` pass-through wrapper: when PDD_E2E_GIT_FETCH_BARE is set, redirects ONLY `fetch`
  // and `push` to the local bare repo so `git remote get-url origin` keeps its canonical GitHub URL.
  writeNodeShim(
    'git',
    `
const { spawnSync } = require('node:child_process');
const args = process.argv.slice(2);
const bare = process.env.PDD_E2E_GIT_FETCH_BARE;
const repoSlug = process.env.PDD_E2E_REPO || 'example/cli-fixture';
const fullArgs = bare && (args[0] === 'fetch' || args[0] === 'push')
  ? ['-c', 'url.file://' + bare + '.insteadOf=https://github.com/' + repoSlug + '.git', ...args]
  : args;
const res = spawnSync(${JSON.stringify(GIT_BIN)}, fullArgs, { stdio: 'inherit' });
process.exit(res.status ?? 1);
`,
  );

  // Also put a symlink to real bin/pdd.mjs in a separate bin dir when tests want `pdd` on PATH.
  return binDir;
}

/** Build a clean isolated environment for spawning bin/pdd.mjs. */
function makeSandboxEnv({ home, shimBin, extraEnv = {} }) {
  const stateDir = join(home, '.local', 'state', 'pdd');
  const suiteQueue = join(home, '.local', 'state', 'pdd-suite-queue');
  const gitConfigGlobal = join(home, '.gitconfig');
  if (!existsSync(gitConfigGlobal)) {
    writeFileSync(gitConfigGlobal, '[user]\n\tname = E2E Fixture\n\temail = fixture@example.invalid\n');
  }
  return {
    PATH: `${shimBin}:${dirname(process.execPath)}:${dirname(GIT_BIN)}:/usr/bin:/bin`,
    HOME: home,
    USERPROFILE: home,
    XDG_CONFIG_HOME: join(home, '.config'),
    XDG_STATE_HOME: join(home, '.local', 'state'),
    XDG_CACHE_HOME: join(home, '.cache'),
    XDG_DATA_HOME: join(home, '.local', 'share'),
    PDD_STATE_DIR: stateDir,
    PDD_SUITE_QUEUE: suiteQueue,
    GH_CONFIG_DIR: join(home, '.config', 'gh'),
    GIT_CONFIG_NOSYSTEM: '1',
    GIT_CONFIG_GLOBAL: gitConfigGlobal,
    PDD_RUNTIME_URL: 'http://127.0.0.1:1',
    PDD_ACCOUNTS_URL: 'http://127.0.0.1:1',
    PDD_NO_OPEN: '1',
    CI: 'true',
    LANG: 'C.UTF-8',
    ...extraEnv,
  };
}

/** Spawn the real bin/pdd.mjs binary with offline network guard and isolated environment. */
function runCli(args, { cwd, home, shimBin, stdin = '', extraEnv = {}, timeoutMs = 15000 } = {}) {
  return new Promise((resolveRun, rejectRun) => {
    const env = makeSandboxEnv({ home, shimBin, extraEnv });
    const child = spawn(process.execPath, ['--import', NET_GUARD, BIN_ENTRY, ...args], {
      cwd,
      env,
      stdio: ['pipe', 'pipe', 'pipe'],
    });
    let stdout = '';
    let stderr = '';
    let settled = false;
    const timer = setTimeout(() => {
      if (settled) return;
      settled = true;
      child.kill('SIGKILL');
      rejectRun(new Error(`pdd ${args.join(' ')} timed out after ${timeoutMs}ms\nstdout:\n${stdout}\nstderr:\n${stderr}`));
    }, timeoutMs);
    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');
    child.stdout.on('data', chunk => { stdout += chunk; });
    child.stderr.on('data', chunk => { stderr += chunk; });
    child.once('error', error => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      rejectRun(error);
    });
    child.once('close', (code, signal) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      resolveRun({ code, signal, stdout, stderr });
    });
    if (stdin !== undefined && stdin !== null) {
      child.stdin.end(stdin);
    } else {
      child.stdin.end();
    }
  });
}

/** Build a synthetic JWT suitable for Codex auth.json fixtures. */
function makeSyntheticJwt(email, accountId) {
  const header = Buffer.from(JSON.stringify({ alg: 'none', typ: 'JWT' })).toString('base64url');
  const payload = Buffer.from(
    JSON.stringify({
      sub: `auth0|${accountId}`,
      email,
      exp: Math.floor(Date.now() / 1000) + 7200,
      'https://api.openai.com/auth': { chatgpt_account_id: accountId, chatgpt_plan_type: 'pro' },
    }),
  ).toString('base64url');
  return `${header}.${payload}.sig`;
}

/** Build a clean reusable core PDD fixture Git repository (CLI code, contracts, SVG, Short JSON, bindings). */
function buildCoreRepoTemplate(baseDir) {
  const repo = join(baseDir, 'core-template');
  mkdirSync(repo, { recursive: true });
  runGit(repo, ['init', '-q', '-b', 'main']);
  runGit(repo, ['remote', 'add', 'origin', 'https://github.com/example/cli-fixture.git']);

  const itemSchema = {
    type: 'object',
    properties: {
      id: { type: 'string' },
      name: { type: 'string' },
      count: { type: 'integer' },
    },
    required: ['id', 'name', 'count'],
    additionalProperties: false,
  };

  writeText(
    repo,
    'contracts/item.md',
    `# Shared items\n\n### item_record\n\`\`\`json\n${JSON.stringify(itemSchema)}\n\`\`\`\n`,
  );

  writeText(
    repo,
    'views/panel.ui.svg',
    `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 360 180" role="img" aria-labelledby="t d">
  <title id="t">CLI fixture panel</title>
  <desc id="d">Minimal clean panel layout for local SVG lint.</desc>
  <rect width="360" height="180" rx="12" fill="#ffffff"/>
  <text x="20" y="42" font-size="20">CLI Fixture</text>
  <rect x="20" y="64" width="320" height="84" rx="8" fill="#f7f7f7" stroke="#cccccc"/>
  <text x="36" y="108" font-size="16">Status: Ready</text>
</svg>\n`,
  );

  const appIface = {
    status: 'draft',
    prose_sha256: 'HASH',
    entries: [
      {
        operation: 'main',
        implementation: { kind: 'cli', command: 'node app.mjs' },
        input_schema: {
          type: 'object',
          properties: {
            argv: { type: 'array', items: { type: 'string' } },
            stdin: { type: 'string' },
          },
          required: ['argv'],
          additionalProperties: false,
        },
        result_schema: {
          type: 'object',
          properties: {
            stdout: { type: 'string' },
            stderr: { type: 'string' },
            exit_code: { type: 'integer' },
          },
          required: ['stdout', 'stderr', 'exit_code'],
          additionalProperties: false,
        },
        errors: ['bad-input'],
      },
    ],
    resources: [],
    conventions: [
      { path: '/entries/0/input_schema', convention: 'cli' },
      { path: '/entries/0/result_schema', convention: 'cli' },
    ],
    calls: [],
    limits: { max_steps: 4, max_model_calls: 2 },
  };
  const appPromptDraft = `# App CLI\n\nOwn \`app.mjs\`.\n\nEchoes the first CLI argument followed by stdin.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(appIface)}\n\`\`\`\n</details>\n`;
  const appPrompt = appPromptDraft.replace('HASH', proseSha256(appPromptDraft));
  writeText(repo, 'prompts/app.prompt.md', appPrompt);

  const appHeaderHash = promptHeaderHash(appPrompt);
  writeText(
    repo,
    'app.mjs',
    `// Generated from prompts/app.prompt.md (sha256: ${appHeaderHash}).
process.stdin.setEncoding('utf8');
let body = '';
for await (const chunk of process.stdin) body += chunk;
if (process.argv[2] === '--fail') {
  process.stderr.write('forced failure\\n');
  process.exitCode = 2;
} else {
  process.stdout.write((process.argv[2] ?? '') + body);
}
`,
  );

  // Second prompt with a linked SVG drawing + inline schema copy matching contracts/item.md#item_record
  // so `pdd contracts`, `pdd contracts sync`, and `pdd lint --local` all exercise real data.
  const linkedIface = {
    status: 'draft',
    prose_sha256: 'HASH',
    entries: [
      {
        operation: 'summarize',
        input_schema: itemSchema,
        result_schema: {
          type: 'object',
          properties: { summary: { type: 'string' } },
          required: ['summary'],
          additionalProperties: false,
        },
        errors: [],
      },
    ],
    resources: [],
    conventions: [],
    calls: [],
    limits: { max_steps: 4, max_model_calls: 2 },
  };
  const linkedDraft = `# Item summary\n\nOwn \`prose-owned.mjs\`.\n\nVisual drawing: [Panel](../views/panel.ui.svg).\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(linkedIface)}\n\`\`\`\n</details>\n`;
  const linkedPrompt = linkedDraft.replace('HASH', proseSha256(linkedDraft));
  writeText(repo, 'prompts/linked.prompt.md', linkedPrompt);
  writeText(repo, 'prose-owned.mjs', 'export const ok = true;\n');
  writeText(repo, 'bound.mjs', 'export const bound = true;\n');
  writeText(repo, 'README.md', '# Fixture Repository\n');
  writeText(
    repo,
    'pdd-bindings.json',
    JSON.stringify(
      {
        schema_version: 'pdd.bindings.v1',
        modules: [{ module: 'bound.mjs', stories: ['user_stories/demo.md'], prompt: 'prompts/app.prompt.md' }],
      },
      null,
      2,
    ) + '\n',
  );
  writeText(repo, 'pdd.json', JSON.stringify({ autopilot: { mode: 'off', trust: [] } }, null, 2) + '\n');

  writeText(
    repo,
    'user_stories/demo.md',
    '# Demo CLI\n\nAs a developer running the echo command, I want the command to print my input text back to stdout.\n\n## Acceptance criteria\n\n1. Passing hello prints hello.\n',
  );
  writeText(
    repo,
    'tests/demo.json',
    JSON.stringify(
      {
        schema_version: 'prompt-runtime.program-scenario.v1',
        story_path: 'user_stories/demo.md',
        criteria: [{ id: 'AC1', text: 'Passing hello prints hello.' }],
        initial_world: {},
        simulation: {},
        context: [],
        steps: [
          {
            step_id: 'echo-hello',
            entry_path: 'prompts/app.prompt.md',
            operation: 'main',
            input: { argv: ['hello'], stdin: '\n' },
            checks: [
              { criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'hello\n' },
              { criterion_id: 'AC1', target: 'result', path: '/exit_code', op: 'equals', value: 0 },
              { criterion_id: 'AC1', target: 'result', path: '/stderr', op: 'equals', value: '' },
            ],
          },
        ],
      },
      null,
      2,
    ) + '\n',
  );

  // Short JSON scenario for `pdd lint --emit-v1` and `pdd lint --bind-criteria`.
  writeText(
    repo,
    'user_stories/short-demo.md',
    '# Short Demo\n\nAs a developer running the echo command, I want a short greeting argument to print back to stdout.\n\n## Acceptance criteria\n\n1. Passing hi prints hi.\n',
  );
  writeText(
    repo,
    'tests/short-demo.json',
    JSON.stringify(
      {
        entry_path: 'prompts/app.prompt.md',
        criteria: [{ id: 'AC1', text: 'Passing hi prints hi.' }],
        steps: [
          {
            id: 'echo-hi',
            op: 'main',
            input: { argv: ['hi'], stdin: '\n' },
            checks: {
              AC1: [
                ['result', '/stdout', '=', 'hi\n'],
                ['result', '/exit_code', '=', 0],
                ['result', '/stderr', '=', ''],
              ],
            },
          },
        ],
      },
      null,
      2,
    ) + '\n',
  );

  runGit(repo, ['add', '.']);
  runGit(repo, ['commit', '-qm', 'Initial E2E fixture']);
  const head = runGit(repo, ['rev-parse', 'HEAD']);
  runGit(repo, ['update-ref', 'refs/remotes/origin/main', head]);
  return repo;
}

/** Build a real Git repo copied from examples/coffee-pickup for product & journeys tests. */
function buildProductRepoTemplate(baseDir) {
  const repo = join(baseDir, 'product-template');
  mkdirSync(repo, { recursive: true });
  cpSync(join(PACKAGE_ROOT, 'examples', 'coffee-pickup'), repo, { recursive: true });
  runGit(repo, ['init', '-q', '-b', 'main']);
  runGit(repo, ['remote', 'add', 'origin', 'https://github.com/example/coffee.git']);
  runGit(repo, ['add', '.']);
  runGit(repo, ['commit', '-qm', 'Product fixture']);
  const head = runGit(repo, ['rev-parse', 'HEAD']);
  runGit(repo, ['update-ref', 'refs/remotes/origin/main', head]);
  return repo;
}

/** Start a loopback HTTP stub server covering /v1/version and /v1/accounts* endpoints. */
async function startLoopbackStubServer() {
  const jwt1 = makeSyntheticJwt('primary@example.invalid', 'acct_e2e_1');
  const jwt2 = makeSyntheticJwt('backup@example.invalid', 'acct_e2e_2');
  const state = {
    accounts: [
      {
        account_id: 'acc_primary',
        label: 'e2e-primary',
        provider: 'codex',
        owner: true,
        is_owner: true,
        owner_login: 'e2e-user',
        email: 'primary@example.invalid',
        state: 'ready',
        paused: false,
        revoked: false,
        five_hour_used_pct: 12,
        weekly_used_pct: 20,
        weekly_reset_at: '2026-11-25T00:00:00Z',
        last_refresh_at: '2026-11-18T12:00:00Z',
        shared_with: [],
      },
      {
        account_id: 'acc_backup',
        label: 'e2e-backup',
        provider: 'codex',
        owner: true,
        is_owner: true,
        owner_login: 'e2e-user',
        email: 'backup@example.invalid',
        state: 'ready',
        paused: false,
        revoked: false,
        five_hour_used_pct: 5,
        weekly_used_pct: 10,
        weekly_reset_at: '2026-11-24T00:00:00Z',
        last_refresh_at: '2026-11-18T12:00:00Z',
        shared_with: [],
      },
      {
        account_id: 'acc_shared',
        label: 'e2e-shared',
        provider: 'codex',
        owner: false,
        is_owner: false,
        owner_login: 'teammate',
        email: 'shared@example.invalid',
        state: 'ready',
        paused: false,
        revoked: false,
        five_hour_used_pct: 0,
        weekly_used_pct: 0,
        weekly_reset_at: '2026-11-26T00:00:00Z',
        last_refresh_at: '2026-11-18T12:00:00Z',
        shared_with: [],
      },
      {
        account_id: 'acc_temp',
        label: 'e2e-temp',
        provider: 'codex',
        owner: true,
        is_owner: true,
        owner_login: 'e2e-user',
        email: 'temp@example.invalid',
        state: 'ready',
        paused: false,
        revoked: false,
        five_hour_used_pct: 0,
        weekly_used_pct: 0,
        weekly_reset_at: '2026-11-27T00:00:00Z',
        last_refresh_at: '2026-11-18T12:00:00Z',
        shared_with: [],
      },
    ],
    pending_invites: [
      {
        invite_id: 'inv_e2e_1',
        account_id: 'acc_invited',
        label: 'e2e-invited',
        provider: 'codex',
        owner_login: 'teammate',
      },
    ],
    auditEvents: [
      {
        created_at: '2026-11-18T12:00:00Z',
        event: 'leased',
        actor_login: 'e2e-user',
        detail: 'e2e fixture event',
      },
    ],
  };

  const tokenBundle = (jwt, acctId) => ({
    auth_mode: 'chatgpt',
    tokens: { access_token: jwt, id_token: jwt, refresh_token: `rt_${acctId}`, account_id: acctId },
    last_refresh: new Date().toISOString(),
  });

  const server = http.createServer((req, res) => {
    const url = new URL(req.url, 'http://127.0.0.1');
    const chunks = [];
    req.on('data', chunk => chunks.push(chunk));
    req.on('end', () => {
      const rawBody = Buffer.concat(chunks).toString('utf8');
      let body = {};
      if (rawBody) {
        try { body = JSON.parse(rawBody); } catch {}
      }
      const send = (status, payload) => {
        res.writeHead(status, { 'content-type': 'application/json' });
        res.end(JSON.stringify(payload));
      };

      if (req.method === 'GET' && url.pathname === '/v1/version') {
        return send(200, {
          engine_sha: '0123456789abcdef0123456789abcdef01234567',
          service_sha: 'fedcba9876543210fedcba9876543210fedcba98',
          formats: {
            interface: ['prompt-runtime.interface.v1'],
            test: ['prompt-runtime.program-scenario.v1'],
            app_map: ['prompt-runtime.app-map.v1'],
          },
        });
      }

      if (req.method === 'GET' && url.pathname === '/v1/accounts') {
        return send(200, { accounts: state.accounts, pending_invites: state.pending_invites });
      }

      if (req.method === 'POST' && url.pathname === '/v1/accounts') {
        const label = body.label || `acct-${state.accounts.length + 1}`;
        const created = {
          account_id: `acc_created_${state.accounts.length + 1}`,
          label,
          provider: body.provider || 'codex',
          owner: true,
          is_owner: true,
          owner_login: 'e2e-user',
          email: `${label}@example.invalid`,
          state: 'ready',
          paused: false,
          revoked: false,
          five_hour_used_pct: 0,
          weekly_used_pct: 0,
          weekly_reset_at: '2026-11-28T00:00:00Z',
          last_refresh_at: new Date().toISOString(),
          shared_with: [],
        };
        state.accounts.push(created);
        return send(201, { account: created });
      }

      if (req.method === 'POST' && url.pathname === '/v1/accounts/lease') {
        const skip = new Set(Array.isArray(body.skip_account_ids) ? body.skip_account_ids : []);
        let chosen = body.preferred_label
          ? state.accounts.find(a => a.label === body.preferred_label && !a.revoked)
          : state.accounts.find(a => a.provider === (body.provider || 'codex') && !a.revoked && !a.paused && !skip.has(a.account_id));
        chosen ??= state.accounts.find(a => !a.revoked);
        const jwt = chosen?.account_id === 'acc_backup' ? jwt2 : jwt1;
        const bundle = tokenBundle(jwt, chosen?.account_id ?? 'acct_e2e_1');
        return send(200, {
          state: 'leased',
          account: chosen,
          lease: {
            lease_id: 'lease_e2e_1',
            account_id: chosen.account_id,
            expires_at: new Date(Date.now() + 3600_000).toISOString(),
            codex_auth_json: bundle,
          },
          auth_json: bundle,
          bundle,
        });
      }

      const acctAction = /^\/v1\/accounts\/([^/]+)\/(pause|unpause|share|unshare|leave|log|usage-report)$/.exec(url.pathname);
      if (acctAction) {
        const [, rawId, action] = acctAction;
        const id = decodeURIComponent(rawId);
        const target = state.accounts.find(a => a.account_id === id);
        if (!target) return send(404, { error: 'not_found' });
        if (action === 'pause') { target.paused = true; return send(200, { ok: true, account: target }); }
        if (action === 'unpause') { target.paused = false; return send(200, { ok: true, account: target }); }
        if (action === 'share') return send(200, { ok: true, invite_id: 'inv_shared_1' });
        if (action === 'unshare') return send(200, { ok: true });
        if (action === 'leave') { target.revoked = true; return send(200, { ok: true }); }
        if (action === 'log') return send(200, { account_id: target.account_id, label: target.label, entries: state.auditEvents });
        if (action === 'usage-report') return send(200, { ok: true });
      }

      const inviteAccept = /^\/v1\/accounts\/invites\/([^/]+)\/accept$/.exec(url.pathname);
      if (req.method === 'POST' && inviteAccept) {
        const inviteId = decodeURIComponent(inviteAccept[1]);
        const inv = state.pending_invites.find(i => i.invite_id === inviteId);
        state.pending_invites = state.pending_invites.filter(i => i.invite_id !== inviteId);
        const accepted = {
          account_id: inv?.account_id ?? 'acc_invited',
          label: inv?.label ?? 'e2e-invited',
          provider: inv?.provider ?? 'codex',
          owner: false,
          is_owner: false,
          owner_login: 'teammate',
          state: 'ready',
          paused: false,
          revoked: false,
          last_refresh_at: new Date().toISOString(),
        };
        state.accounts.push(accepted);
        return send(200, { ok: true, account: accepted });
      }

      const delMatch = /^\/v1\/accounts\/([^/]+)$/.exec(url.pathname);
      if (req.method === 'DELETE' && delMatch) {
        const id = decodeURIComponent(delMatch[1]);
        state.accounts = state.accounts.filter(a => a.account_id !== id);
        return send(200, { ok: true });
      }

      return send(404, { error: `Unhandled stub route: ${req.method} ${url.pathname}` });
    });
  });

  await new Promise(resolveListen => server.listen(0, '127.0.0.1', resolveListen));
  activeServers.push(server);
  const { port } = server.address();
  return { server, baseUrl: `http://127.0.0.1:${port}`, state };
}

// Shared immutable templates & shim bin created once for fast test execution.
const SUITE_ROOT = makeTempDir('pdd-cli-e2e-suite-');
const SHIM_BIN = createShimBin(SUITE_ROOT);
const CORE_TEMPLATE = buildCoreRepoTemplate(SUITE_ROOT);
const PRODUCT_TEMPLATE = buildProductRepoTemplate(SUITE_ROOT);

/** Clone a clean temp repository and dedicated temp HOME for an isolated test block. */
function makeIsolatedFixture(label, template = CORE_TEMPLATE) {
  const dir = makeTempDir(`pdd-e2e-${label}-`);
  const repo = join(dir, 'repo');
  const home = join(dir, 'home');
  mkdirSync(home, { recursive: true });
  cpSync(template, repo, { recursive: true });
  return {
    dir,
    repo,
    home,
    cli: (args, opts = {}) =>
      runCli(args, { cwd: opts.cwd ?? repo, home, shimBin: SHIM_BIN, ...opts }),
  };
}

// Tracks every catalog route ID that actually executes a real bin/pdd.mjs subprocess test.
const executedRoutes = new Set();
const markExecuted = routeId => {
  assert.ok(PUBLIC_COMMAND_IDS.includes(routeId), `Unknown route ID in E2E suite: ${routeId}`);
  executedRoutes.add(routeId);
};

// Static manifest of every route ID covered by the executable tests below.
// Fails immediately if a new public command is added to src/command-catalog.mjs without E2E coverage.
const REGISTERED_E2E_ROUTES = Object.freeze([
  // Discovery, help, version, completion
  'help', 'version', 'version.detailed', 'completion',
  // Core PDD workflow
  'setup', 'init', 'status', 'check', 'lint', 'prove', 'try', 'files', 'owner', 'update', 'contracts', 'contracts.sync', 'jobs', 'mcp', 'upgrade',
  // Cloud accounts
  'accounts', 'accounts.list', 'accounts.status', 'accounts.add', 'accounts.import', 'accounts.use',
  'accounts.next', 'accounts.codex', 'accounts.sync', 'accounts.auto', 'accounts.pause', 'accounts.unpause',
  'accounts.share', 'accounts.accept', 'accounts.unshare', 'accounts.leave', 'accounts.remove', 'accounts.log',
  // Product
  'product.status', 'product.next', 'product.start', 'product.contracts',
  // Graph
  'graph',
  // Autopilot
  'autopilot.doctor', 'autopilot.start', 'autopilot.suite', 'autopilot.status', 'autopilot.logs', 'autopilot.stop',
  'autopilot.observe', 'autopilot.auto', 'autopilot.off', 'autopilot.trust', 'autopilot.untrust',
  'autopilot.add', 'autopilot.release', 'autopilot.intake', 'autopilot.graph', 'autopilot.report', 'autopilot.regressions',
  'autopilot.alerts', 'autopilot.alert', 'autopilot.check-base',
  // Metrics
  'metrics', 'metrics.stages', 'metrics.skills', 'metrics.full', 'metrics.on', 'metrics.off',
]);

test('catalog completeness guard: every public command in src/command-catalog.mjs has an E2E entry', () => {
  const catalogIds = [...PUBLIC_COMMAND_IDS].sort();
  const registeredIds = [...new Set(REGISTERED_E2E_ROUTES)].sort();
  assert.equal(REGISTERED_E2E_ROUTES.length, registeredIds.length, 'Duplicate route IDs in REGISTERED_E2E_ROUTES');
  const missing = catalogIds.filter(id => !registeredIds.includes(id));
  const extra = registeredIds.filter(id => !catalogIds.includes(id));
  assert.deepEqual(missing, [], `Catalog routes missing E2E coverage: ${missing.join(', ')}`);
  assert.deepEqual(extra, [], `Stale E2E route entries absent from catalog: ${extra.join(', ')}`);
});

describe('CLI surface E2E execution', { concurrency: 4 }, () => {
test('every public command renders focused --help via real bin/pdd.mjs subprocess', async () => {
  const fx = makeIsolatedFixture('help-all');
  const helpTargets = PUBLIC_COMMAND_ROUTES.filter(
    route => !['help', 'version', 'version.detailed'].includes(route.id),
  );
  const results = await runPool(helpTargets, 8, async route => {
    const res = await fx.cli([...route.prefix, '--help']);
    return { route, res };
  });
  for (const { route, res } of results) {
    assert.equal(res.code, 0, `${route.id} (--help) exited ${res.code}: ${res.stderr}`);
    const unwrappedHelp = res.stdout.replace(/\|\n      /g, '|').replace(/\n      /g, ' ');
    for (const entry of route.forms) {
      assert.ok(
        unwrappedHelp.includes(entry.form),
        `${route.id} --help missing documented form: ${entry.form}\nActual stdout:\n${res.stdout}`,
      );
    }
  }
});

test('discovery, help, version, and shell completion commands work end-to-end', async () => {
  const fx = makeIsolatedFixture('discovery');

  // help: bare pdd, --help, -h, help, help prompting, group help
  for (const args of [[], ['--help'], ['-h'], ['help']]) {
    const res = await fx.cli(args);
    assert.equal(res.code, 0, `pdd ${args.join(' ')} failed: ${res.stderr}`);
    assert.match(res.stdout, /Usage: pdd <command> \[options\]/);
    assert.match(res.stdout, /Core PDD workflow:/);
    assert.match(res.stdout, /Autopilot \(pdd autopilot --help\):/);
  }
  const promptingHelp = await fx.cli(['help', 'prompting']);
  assert.equal(promptingHelp.code, 0, promptingHelp.stderr);
  assert.match(promptingHelp.stdout, /In PDD, prompts are the source/);
  const productGroupHelp = await fx.cli(['product', '--help']);
  assert.equal(productGroupHelp.code, 0, productGroupHelp.stderr);
  assert.match(productGroupHelp.stdout, /pdd product status/);
  markExecuted('help');

  // version: --version and quiet -V
  for (const flag of ['--version', '-V']) {
    const res = await fx.cli([flag]);
    assert.equal(res.code, 0, `${flag}: ${res.stderr}`);
    assert.equal(res.stdout.trim(), PKG_VERSION);
  }
  markExecuted('version');

  // version.detailed: offline unknown + loopback /v1/version metadata
  const offlineVV = await fx.cli(['-VV']);
  assert.equal(offlineVV.code, 0, offlineVV.stderr);
  assert.equal(offlineVV.stdout, `PDD CLI: ${PKG_VERSION}\nPDD interpreter: unknown\n`);

  const stub = await startLoopbackStubServer();
  const onlineVV = await fx.cli(['-VV'], {
    extraEnv: { PDD_RUNTIME_URL: stub.baseUrl, PDD_E2E_FAKE_GH: 'ok' },
  });
  assert.equal(onlineVV.code, 0, onlineVV.stderr);
  assert.ok(onlineVV.stdout.includes(`PDD CLI: ${PKG_VERSION}\n`), onlineVV.stdout);
  assert.match(onlineVV.stdout, /PDD interpreter: 0123456789abcdef0123456789abcdef01234567/);
  assert.match(onlineVV.stdout, /PDD service: fedcba9876543210fedcba9876543210fedcba98/);
  assert.match(onlineVV.stdout, /Interface formats: prompt-runtime\.interface\.v1/);
  markExecuted('version.detailed');

  // completion: bash & zsh
  for (const shell of ['bash', 'zsh']) {
    const res = await fx.cli(['completion', shell]);
    assert.equal(res.code, 0, `completion ${shell}: ${res.stderr}`);
    assert.match(res.stdout, /setup/);
    assert.match(res.stdout, /product/);
    assert.match(res.stdout, /autopilot/);
  }
  markExecuted('completion');
});

test('core local authoring commands: setup, init, status, files, owner, contracts, jobs, mcp, upgrade', async () => {
  const fx = makeIsolatedFixture('core-local');

  // setup --yes: laptop-only — installs global skills to temp HOME without touching repo files
  const setup1 = await fx.cli(['setup', '--yes']);
  assert.equal(setup1.code, 0, setup1.stderr);
  assert.match(setup1.stdout, /Installed 1 PDD skill\b/);
  assert.ok(existsSync(join(fx.home, '.agents', 'skills', 'pdd', 'SKILL.md')));
  assert.ok(existsSync(join(fx.home, '.agents', 'skills', 'pdd', '.pdd-skill.json')));
  assert.ok(existsSync(join(fx.home, '.claude', 'skills', 'pdd', 'SKILL.md')));
  assert.ok(existsSync(join(fx.home, '.gemini', 'config', 'skills', 'pdd', 'SKILL.md')));
  assert.equal(existsSync(join(fx.repo, 'AGENTS.md')), false, 'setup never writes repo AGENTS.md');
  // Repeat setup is idempotent
  const setup2 = await fx.cli(['setup', '--yes']);
  assert.equal(setup2.code, 0, setup2.stderr);
  assert.match(setup2.stdout, /PDD skills found in/);
  markExecuted('setup');

  // init: per-repo setup adds the 4-line PDD block to AGENTS.md without editing root .gitignore
  const init1 = await fx.cli(['init']);
  assert.equal(init1.code, 0, init1.stderr);
  const agentsMd = readFileSync(join(fx.repo, 'AGENTS.md'), 'utf8');
  assert.match(agentsMd, /<!-- pdd:start -->[\s\S]*<!-- pdd:end -->/);
  const init2 = await fx.cli(['init']);
  assert.equal(init2.code, 0, init2.stderr);
  assert.match(init2.stdout, /already has this PDD block\. No change\./);
  markExecuted('init');

  // status & status --json (offline repo overview + pdd.json verify.paths Feature Map)
  const statusText = await fx.cli(['status']);
  assert.equal(statusText.code, 0, statusText.stderr);
  assert.match(statusText.stdout, /PDD status: \d+ prompts?, \d+ Stor(?:y|ies), \d+ tests?/);
  const statusJson = await fx.cli(['status', 'app.mjs', '--json']);
  assert.equal(statusJson.code, 0, statusJson.stderr);
  const statusData = JSON.parse(statusJson.stdout);
  assert.equal(statusData.schema_version, 'pdd.status.v1');
  assert.equal(statusData.has_pdd_block, true);
  assert.equal(statusData.files[0].owner, 'prompts/app.prompt.md');
  markExecuted('status');

  // files & files --json
  const filesText = await fx.cli(['files']);
  assert.equal(filesText.code, 0, filesText.stderr);
  assert.match(filesText.stdout, /Prompt: prompts\/app\.prompt\.md/);
  assert.match(filesText.stdout, /Story: user_stories\/demo\.md/);
  const filesJson = await fx.cli(['files', '--json']);
  assert.equal(filesJson.code, 0, filesJson.stderr);
  const filesData = JSON.parse(filesJson.stdout);
  assert.equal(filesData.schema_version, 'pdd.files.v1');
  assert.ok(filesData.prompts.some(p => p.path === 'prompts/app.prompt.md' && p.has_interface === true));
  assert.ok(filesData.stories.some(s => s.path === 'user_stories/demo.md'));
  assert.ok(filesData.tests.some(t => t.path === 'tests/demo.json'));
  markExecuted('files');

  // owner & owner --json (binding, header, prose-advisory, and unowned)
  const ownerRes = await fx.cli(['owner', 'bound.mjs', 'app.mjs', 'prose-owned.mjs', 'README.md', '--json']);
  assert.equal(ownerRes.code, 0, ownerRes.stderr);
  const ownerData = JSON.parse(ownerRes.stdout);
  assert.equal(ownerData.schema_version, 'pdd.owner.v1');
  const byPath = Object.fromEntries(ownerData.files.map(row => [row.path, row]));
  assert.equal(byPath['bound.mjs'].source, 'binding');
  assert.equal(byPath['bound.mjs'].owner, 'prompts/app.prompt.md');
  assert.equal(byPath['app.mjs'].source, 'header');
  assert.equal(byPath['app.mjs'].headers[0].state, 'current');
  assert.equal(byPath['prose-owned.mjs'].owner, null);
  assert.equal(byPath['prose-owned.mjs'].source, null);
  assert.equal(byPath['prose-owned.mjs'].certain, true);
  assert.match(byPath['prose-owned.mjs'].note, /\/\/ Prompt:/);
  assert.equal(byPath['README.md'].owner, null);
  const ownerText = await fx.cli(['owner', 'app.mjs']);
  assert.equal(ownerText.code, 0, ownerText.stderr);
  assert.match(ownerText.stdout, /app\.mjs: prompts\/app\.prompt\.md \(header\)/);
  markExecuted('owner');

  // update: read-only changed-map report, --check clean pass, and --write refusal (exit 2)
  const updatePlan = await fx.cli(['update', 'app.mjs', 'README.md', '--json']);
  assert.equal(updatePlan.code, 0, updatePlan.stderr);
  const planData = JSON.parse(updatePlan.stdout);
  assert.equal(planData.schema_version, 'pdd.update-sync.v1');
  assert.equal(planData.prompts[0].prompt, 'prompts/app.prompt.md');
  assert.equal(planData.modules[0].status, 'current');
  assert.deepEqual(planData.unowned, [{ path: 'README.md', reason: 'no owning prompt' }]);
  const updateCheckPass = await fx.cli(['update', 'app.mjs', '--check', '--json']);
  assert.equal(updateCheckPass.code, 0, updateCheckPass.stderr);
  assert.equal(JSON.parse(updateCheckPass.stdout).ok, true);
  const updateWrite = await fx.cli(['update', 'app.mjs', '--write', '--json']);
  assert.equal(updateWrite.code, 2, updateWrite.stderr);
  assert.match(updateWrite.stderr, /read-only|Invariant:/i);
  markExecuted('update');

  // contracts & contracts sync [--write]
  const contractsRes = await fx.cli(['contracts']);
  assert.equal(contractsRes.code, 0, contractsRes.stderr);
  assert.match(contractsRes.stdout, /contracts\/item\.md#item_record/);
  markExecuted('contracts');

  const syncPreview = await fx.cli(['contracts', 'sync']);
  assert.equal(syncPreview.code, 0, syncPreview.stderr);
  assert.match(syncPreview.stdout, /prompts\/linked\.prompt\.md .* -> contracts\/item\.md#item_record/);
  assert.match(syncPreview.stdout, /Preview: 1 files\. Use --write to apply\./);
  const syncWrite = await fx.cli(['contracts', 'sync', '--write']);
  assert.equal(syncWrite.code, 0, syncWrite.stderr);
  assert.match(readFileSync(join(fx.repo, 'prompts', 'linked.prompt.md'), 'utf8'), /"\$contract":\s*"contracts\/item\.md#item_record"/);
  const syncAfter = await fx.cli(['contracts', 'sync']);
  assert.equal(syncAfter.code, 0, syncAfter.stderr);
  assert.match(syncAfter.stdout, /Preview: 0 files\./);
  markExecuted('contracts.sync');

  // jobs: clean empty state
  const jobsRes = await fx.cli(['jobs']);
  assert.equal(jobsRes.code, 0, jobsRes.stderr);
  assert.equal(jobsRes.stdout.trim(), 'No local interpreter jobs.');
  markExecuted('jobs');

  // mcp: real stdio JSON-RPC initialize + ping + tools/list
  const mcpRequests = [
    JSON.stringify({
      jsonrpc: '2.0',
      id: 1,
      method: 'initialize',
      params: { protocolVersion: '2025-06-18', capabilities: {}, clientInfo: { name: 'cli-e2e', version: '1.0' } },
    }),
    JSON.stringify({ jsonrpc: '2.0', id: 2, method: 'ping', params: {} }),
    JSON.stringify({ jsonrpc: '2.0', id: 3, method: 'tools/list', params: {} }),
  ].join('\n') + '\n';
  const mcpRes = await fx.cli(['mcp'], { stdin: mcpRequests });
  assert.equal(mcpRes.code, 0, mcpRes.stderr);
  const mcpReplies = mcpRes.stdout.trim().split('\n').map(line => JSON.parse(line));
  assert.equal(mcpReplies.length, 3);
  assert.equal(mcpReplies[0].result.serverInfo.name, 'pdd-try');
  assert.equal(mcpReplies[0].result.serverInfo.version, PKG_VERSION);
  assert.deepEqual(mcpReplies[1].result, {});
  assert.ok(Array.isArray(mcpReplies[2].result.tools) && mcpReplies[2].result.tools.length > 0);
  markExecuted('mcp');

  // Removed `pdd approve` exits 2 cleanly with a helpful pointer to chat / GitHub PR review and zero file edits
  const appBefore = readFileSync(join(fx.repo, 'prompts', 'app.prompt.md'), 'utf8');
  const approveRemoved = await fx.cli(['approve', 'prompts/app.prompt.md']);
  assert.equal(approveRemoved.code, 2, approveRemoved.stderr);
  assert.equal(approveRemoved.stdout, '');
  assert.match(approveRemoved.stderr, /pdd approve was removed.*chat or GitHub PR review/i);
  assert.equal(readFileSync(join(fx.repo, 'prompts', 'app.prompt.md'), 'utf8'), appBefore);
  const rootHelp = await fx.cli(['--help']);
  assert.equal(rootHelp.code, 0, rootHelp.stderr);
  const rootHelpBody = rootHelp.stdout.split('\n').filter(line => !/^(?:Skill|Prompting guide): /.test(line)).join('\n');
  assert.doesNotMatch(rootHelpBody, /\bapprove\b/i);

  // upgrade & upgrade --main: refuses source Git checkout cleanly without touching npm or network
  for (const args of [['upgrade'], ['upgrade', '--main']]) {
    const res = await fx.cli(args);
    assert.equal(res.code, 1);
    assert.match(res.stderr, /user-owned global npm installation/);
  }
  markExecuted('upgrade');
});

test('test, lint, and simulate commands exercise local modes and flag combinations end-to-end', async () => {
  const fx = makeIsolatedFixture('test-lint-sim');

  // pdd test --target code (JSON + text) on real CLI fixture
  const codeJson = await fx.cli(['test', '--target', 'code', 'demo', '--json']);
  assert.equal(codeJson.code, 0, codeJson.stderr);
  const codeReport = JSON.parse(codeJson.stdout);
  assert.equal(codeReport.target, 'code');
  assert.equal(codeReport.ai_calls, 0);
  assert.equal(codeReport.stories[0].status, 'passed');
  assert.ok(existsSync(join(fx.repo, '.pdd', 'code-test', 'latest.json')));

  const codeText = await fx.cli(['test', '--target', 'code', 'demo']);
  assert.equal(codeText.code, 0, codeText.stderr);
  assert.match(codeText.stdout, /PASSED\s+user_stories\/demo\.md/);

  // pdd test --files [--json] (offline upload preview)
  const filesPreview = await fx.cli(['test', '--files', 'demo', '--json']);
  assert.equal(filesPreview.code, 0, filesPreview.stderr);
  const previewPayload = JSON.parse(filesPreview.stdout);
  assert.ok(JSON.stringify(previewPayload).includes('prompts/app.prompt.md'));
  assert.ok(JSON.stringify(previewPayload).includes('tests/demo.json'));

  // pdd test --explain-bindings [--json] (offline)
  const explainRes = await fx.cli(['test', '--explain-bindings', 'demo', '--json']);
  assert.equal(explainRes.code, 0, explainRes.stderr);
  assert.doesNotThrow(() => JSON.parse(explainRes.stdout));

  // pdd test --read and --retry offline clean handling
  const readRes = await fx.cli(['test', '--read', '--json']);
  assert.notEqual(readRes.code, 3, `unexpected internal crash on --read: ${readRes.stderr}`);
  const retryRes = await fx.cli(['test', '--retry', 'missing-batch-id']);
  assert.notEqual(retryRes.code, 0);
  assert.doesNotMatch(retryRes.stderr, /ReferenceError|TypeError|SyntaxError/);

  // pdd test --affected, --lf, --screen/--drawing/--look, and full-flag boundary checks (offline)
  const affectedRes = await fx.cli([
    'test', '--affected', '--cache-clear', '--details', '--timeout', '1', '--max-calls', '18',
    '--max-total-calls', '40', '--no-restart-replacement',
  ]);
  assert.notEqual(affectedRes.code, 2, `valid flags rejected as parser error: ${affectedRes.stderr}`);
  assert.doesNotMatch(affectedRes.stderr, /ReferenceError|TypeError|SyntaxError/);

  const lfRes = await fx.cli(['test', '--lf']);
  assert.notEqual(lfRes.code, 2, `valid --lf flag rejected: ${lfRes.stderr}`);
  assert.doesNotMatch(lfRes.stderr, /ReferenceError|TypeError|SyntaxError/);

  const screenRes = await fx.cli(['test', '--screen', 'missing-shot.png', '--drawing', 'views/panel.ui.svg', '--look']);
  assert.notEqual(screenRes.code, 0);
  assert.doesNotMatch(screenRes.stderr, /ReferenceError|TypeError|SyntaxError/);
  markExecuted('check');

  // pdd lint --local [--json] (0 network, checks SVG layout)
  const lintLocal = await fx.cli(['lint', '--local', '--json']);
  assert.equal(lintLocal.code, 0, lintLocal.stderr);
  const lintLocalData = JSON.parse(lintLocal.stdout);
  assert.equal(lintLocalData.exit_code, 0);
  assert.equal(lintLocalData.local_only, true);
  assert.deepEqual(lintLocalData.problems, []);

  // pdd lint --emit-v1 (0 network, expands Short JSON to program-scenario.v1)
  const emitV1 = await fx.cli(['lint', '--emit-v1', 'short-demo']);
  assert.equal(emitV1.code, 0, emitV1.stderr);
  assert.match(emitV1.stdout, /"schema_version":\s*"prompt-runtime\.program-scenario\.v1"/);
  assert.match(emitV1.stdout, /"step_id":\s*"echo-hi"/);
  assert.match(emitV1.stdout, /"criterion_id":\s*"AC1"/);

  // pdd lint --bind-criteria [--json] (0 network, binds AC1 -> ac-sha256-... on disk)
  const bindRes = await fx.cli(['lint', '--bind-criteria', 'short-demo', '--json']);
  assert.equal(bindRes.code, 0, bindRes.stderr);
  assert.match(readFileSync(join(fx.repo, 'tests', 'short-demo.json'), 'utf8'), /ac-sha256-/);

  // pdd lint --emit-v1 --write [--json] (0 network, writes expanded v1 JSON to disk)
  const emitWriteRes = await fx.cli(['lint', '--emit-v1', '--write', 'short-demo', '--json']);
  assert.equal(emitWriteRes.code, 0, emitWriteRes.stderr);
  assert.match(
    readFileSync(join(fx.repo, 'tests', 'short-demo.json'), 'utf8'),
    /"schema_version":\s*"prompt-runtime\.program-scenario\.v1"/,
  );

  // pdd lint --codex --json --timeout 1 (runs through codex-lint with safe codex shim)
  const codexLint = await fx.cli(['lint', '--codex', 'demo', '--json', '--timeout', '1']);
  assert.notEqual(codexLint.code, 2, `valid lint --codex flags failed parser: ${codexLint.stderr}`);
  assert.doesNotMatch(codexLint.stderr, /ReferenceError|TypeError|SyntaxError/);
  markExecuted('lint');

  // pdd prove --json (stateless offline proof against base ref)
  const proveLocal = await fx.cli(['prove', '--json']);
  assert.ok([0, 1, 3].includes(proveLocal.code), `unexpected pdd prove exit ${proveLocal.code}: ${proveLocal.stderr}`);
  assert.equal(JSON.parse(proveLocal.stdout).schema_version, 'pdd.prove.v1');
  markExecuted('prove');

  // pdd product contracts (alias for pdd contracts)
  const prodContracts = await fx.cli(['product', 'contracts']);
  assert.equal(prodContracts.code, 0, prodContracts.stderr);
  markExecuted('product.contracts');

  // pdd simulate (and quiet alias pdd sim): offline --stop and --save-last
  const simStop = await fx.cli(['simulate', '--stop', 'demo']);
  assert.equal(simStop.code, 2, simStop.stderr);
  assert.match(simStop.stderr, /No open Try for "demo"/);

  const simQuietStop = await fx.cli(['sim', '--stop', 'demo']);
  assert.equal(simQuietStop.code, simStop.code);
  assert.equal(simQuietStop.stderr, simStop.stderr);

  const simSaveLast = await fx.cli(['simulate', '--save-last']);
  assert.notEqual(simSaveLast.code, 0);
  assert.doesNotMatch(simSaveLast.stderr, /ReferenceError|TypeError|SyntaxError/);

  // Flag combination acceptance on simulate (offline unreachable runtime fails cleanly, not exit 2)
  const simOffline = await fx.cli([
    'simulate', 'demo', '--tab', 'call', '--max-calls', '20', '--no-open', '--no-wait', '--new',
  ]);
  assert.notEqual(simOffline.code, 2, `valid simulate flags rejected: ${simOffline.stderr}`);
  assert.doesNotMatch(simOffline.stderr, /ReferenceError|TypeError|SyntaxError/);

  const simCliMode = await fx.cli(['simulate', 'demo', '--cli', '--no-open', '--no-wait']);
  assert.notEqual(simCliMode.code, 2, `valid simulate --cli flags rejected: ${simCliMode.stderr}`);
  assert.doesNotMatch(simCliMode.stderr, /ReferenceError|TypeError|SyntaxError/);
  markExecuted('try');
});

test('all 18 cloud accounts commands work end-to-end (offline guards + loopback Cloud API)', async () => {
  const fx = makeIsolatedFixture('accounts');

  // 1. Offline-safe local commands (zero server, unreachable PDD_ACCOUNTS_URL)
  const offlineStatus = await fx.cli(['accounts', 'status', '--json']);
  assert.equal(offlineStatus.code, 0, offlineStatus.stderr);
  const offlineStatusJson = JSON.parse(offlineStatus.stdout);
  assert.equal(offlineStatusJson.enrolled, false);

  const offlineSync = await fx.cli(['accounts', 'sync', '--provider', 'codex', '--quiet', '--timeout-ms', '120']);
  assert.equal(offlineSync.code, 0, `accounts sync must fail-open when offline: ${offlineSync.stderr}`);

  // accounts auto status -> on -> status -> off -> status inside temp HOME
  const autoBefore = await fx.cli(['accounts', 'auto', 'status']);
  assert.equal(autoBefore.code, 0, autoBefore.stderr);
  assert.match(autoBefore.stdout, /off/i);

  const autoOn = await fx.cli(['accounts', 'auto', 'on']);
  assert.equal(autoOn.code, 0, autoOn.stderr);
  assert.match(readFileSync(join(fx.home, '.zshrc'), 'utf8'), /# >>> pdd accounts auto >>>/);

  const autoAfterOn = await fx.cli(['accounts', 'auto', 'status']);
  assert.equal(autoAfterOn.code, 0, autoAfterOn.stderr);
  assert.match(autoAfterOn.stdout, /on/i);

  const autoOff = await fx.cli(['accounts', 'auto', 'off']);
  assert.equal(autoOff.code, 0, autoOff.stderr);
  assert.doesNotMatch(readFileSync(join(fx.home, '.zshrc'), 'utf8'), /# >>> pdd accounts auto >>>/);
  markExecuted('accounts.auto');

  // 2. Full loopback Cloud Accounts E2E across all Cloud API routes
  const stub = await startLoopbackStubServer();
  const cloudEnv = { PDD_ACCOUNTS_URL: stub.baseUrl, PDD_TOKEN: 'e2e-cloud-bearer', PDD_E2E_FAKE_GH: 'ok' };

  const rootList = await fx.cli(['accounts', '--json'], { extraEnv: cloudEnv });
  assert.equal(rootList.code, 0, rootList.stderr);
  const rootListJson = JSON.parse(rootList.stdout);
  assert.ok(rootListJson.accounts.some(a => a.label === 'e2e-primary'));
  markExecuted('accounts');

  const subList = await fx.cli(['accounts', 'list'], { extraEnv: cloudEnv });
  assert.equal(subList.code, 0, subList.stderr);
  assert.match(subList.stdout, /e2e-primary/);
  markExecuted('accounts.list');

  const statusOnline = await fx.cli(['accounts', 'status', '--json'], { extraEnv: cloudEnv });
  assert.equal(statusOnline.code, 0, statusOnline.stderr);
  assert.doesNotThrow(() => JSON.parse(statusOnline.stdout));
  markExecuted('accounts.status');

  // accounts add (invokes safe codex shim `codex login` in isolated folder and uploads to stub)
  const addRes = await fx.cli(['accounts', 'add', '--provider', 'codex', '--label', 'e2e-added'], {
    extraEnv: cloudEnv,
  });
  assert.equal(addRes.code, 0, `accounts add failed: ${addRes.stderr}\n${addRes.stdout}`);
  markExecuted('accounts.add');

  // accounts import --from <synthetic auth.json>
  const authPath = join(fx.dir, 'import-auth.json');
  const importJwt = makeSyntheticJwt('imported@example.invalid', 'acct_e2e_import');
  writeFileSync(
    authPath,
    JSON.stringify({
      auth_mode: 'chatgpt',
      tokens: { access_token: importJwt, id_token: importJwt, refresh_token: 'rt_import', account_id: 'acct_e2e_import' },
      last_refresh: new Date().toISOString(),
    }),
  );
  const importRes = await fx.cli(
    ['accounts', 'import', '--provider', 'codex', '--from', authPath, '--label', 'e2e-imported'],
    { extraEnv: cloudEnv },
  );
  assert.equal(importRes.code, 0, `accounts import failed: ${importRes.stderr}\n${importRes.stdout}`);
  markExecuted('accounts.import');

  // accounts use
  const useRes = await fx.cli(['accounts', 'use', 'e2e-primary', '--provider', 'codex'], { extraEnv: cloudEnv });
  assert.equal(useRes.code, 0, useRes.stderr);
  assert.match(useRes.stdout, /e2e-primary/);
  assert.ok(existsSync(join(fx.home, '.local', 'state', 'pdd', 'codex-home', 'auth.json')));
  markExecuted('accounts.use');

  // accounts next
  const nextRes = await fx.cli(['accounts', 'next', '--provider', 'codex'], { extraEnv: cloudEnv });
  assert.equal(nextRes.code, 0, nextRes.stderr);
  assert.match(nextRes.stdout, /e2e-backup|Switched|Active/i);
  markExecuted('accounts.next');

  // accounts sync online
  const syncOnline = await fx.cli(['accounts', 'sync', '--provider', 'codex', '--timeout-ms', '5000'], {
    extraEnv: cloudEnv,
  });
  assert.equal(syncOnline.code, 0, syncOnline.stderr);
  markExecuted('accounts.sync');

  // accounts pause & unpause
  const pauseRes = await fx.cli(['accounts', 'pause', 'e2e-primary', '--provider', 'codex'], { extraEnv: cloudEnv });
  assert.equal(pauseRes.code, 0, pauseRes.stderr);
  assert.match(pauseRes.stdout, /Paused account "e2e-primary"/);
  markExecuted('accounts.pause');

  const unpauseRes = await fx.cli(['accounts', 'unpause', 'e2e-primary', '--provider', 'codex'], { extraEnv: cloudEnv });
  assert.equal(unpauseRes.code, 0, unpauseRes.stderr);
  assert.match(unpauseRes.stdout, /Unpaused account "e2e-primary"/);
  markExecuted('accounts.unpause');

  // accounts share & unshare (single account + --all flag)
  const shareRes = await fx.cli(
    ['accounts', 'share', 'e2e-primary', '--provider', 'codex', '--with', 'alice'],
    { extraEnv: cloudEnv },
  );
  assert.equal(shareRes.code, 0, shareRes.stderr);
  assert.match(shareRes.stdout, /Shared "e2e-primary" with @?alice/i);
  const shareAllRes = await fx.cli(
    ['accounts', 'share', '--all', '--provider', 'codex', '--with', 'alice'],
    { extraEnv: cloudEnv },
  );
  assert.equal(shareAllRes.code, 0, shareAllRes.stderr);
  markExecuted('accounts.share');

  const unshareRes = await fx.cli(
    ['accounts', 'unshare', 'e2e-primary', '--provider', 'codex', '--user', 'alice'],
    { extraEnv: cloudEnv },
  );
  assert.equal(unshareRes.code, 0, unshareRes.stderr);
  assert.match(unshareRes.stdout, /Revoked "e2e-primary" access for @?alice/i);
  const unshareAllRes = await fx.cli(
    ['accounts', 'unshare', '--all', '--provider', 'codex', '--with', 'alice'],
    { extraEnv: cloudEnv },
  );
  assert.equal(unshareAllRes.code, 0, unshareAllRes.stderr);
  markExecuted('accounts.unshare');

  // accounts accept
  const acceptRes = await fx.cli(['accounts', 'accept', 'inv_e2e_1'], { extraEnv: cloudEnv });
  assert.equal(acceptRes.code, 0, acceptRes.stderr);
  assert.match(acceptRes.stdout, /Accepted shared account "e2e-invited"/);
  markExecuted('accounts.accept');

  // accounts leave
  const leaveRes = await fx.cli(['accounts', 'leave', 'e2e-shared', '--provider', 'codex'], { extraEnv: cloudEnv });
  assert.equal(leaveRes.code, 0, leaveRes.stderr);
  assert.match(leaveRes.stdout, /Left shared account "e2e-shared"/);
  markExecuted('accounts.leave');

  // accounts remove
  const removeRes = await fx.cli(['accounts', 'remove', 'e2e-temp', '--provider', 'codex'], { extraEnv: cloudEnv });
  assert.equal(removeRes.code, 0, removeRes.stderr);
  assert.match(removeRes.stdout, /Removed account "e2e-temp"/);
  markExecuted('accounts.remove');

  // accounts log (--json + text)
  const logJson = await fx.cli(['accounts', 'log', 'e2e-primary', '--provider', 'codex', '--json'], {
    extraEnv: cloudEnv,
  });
  assert.equal(logJson.code, 0, logJson.stderr);
  const logPayload = JSON.parse(logJson.stdout);
  assert.equal(logPayload.label, 'e2e-primary');
  assert.equal(logPayload.entries.length, 1);
  const logText = await fx.cli(['accounts', 'log', 'e2e-primary', '--provider', 'codex'], { extraEnv: cloudEnv });
  assert.equal(logText.code, 0, logText.stderr);
  assert.match(logText.stdout, /leased/);
  markExecuted('accounts.log');

  // accounts codex passthrough invokes safe codex shim with forwarded args & managed CODEX_HOME
  const codexLog = join(fx.dir, 'codex-args.jsonl');
  const codexPass = await fx.cli(['accounts', 'codex', '--', '--version'], {
    extraEnv: { ...cloudEnv, PDD_E2E_CODEX_LOG: codexLog },
  });
  assert.equal(codexPass.code, 0, codexPass.stderr);
  assert.ok(existsSync(codexLog), 'accounts codex must invoke the codex binary');
  const codexEntry = JSON.parse(readFileSync(codexLog, 'utf8').trim());
  assert.deepEqual(codexEntry.args, ['--version']);
  assert.equal(codexEntry.codexHome, join(fx.home, '.local', 'state', 'pdd', 'codex-home'));
  markExecuted('accounts.codex');
});

// Unweakened regression test for a real CLI defect discovered by this E2E suite:
// src/accounts-cli.mjs:runPlainCodexOnce (lines 4056-4081) runs `codex` via piped runAgentProcess(...)
// in non-TTY mode and returns `{ exitCode, message: '' }`, silently dropping all child stdout/stderr.
test('regression: pdd accounts codex forwards child stdout/stderr in non-TTY mode (known bug in src/accounts-cli.mjs)', async () => {
  const fx = makeIsolatedFixture('accounts-codex-stdout');
  const codexLog = join(fx.dir, 'codex-args.jsonl');
  const res = await fx.cli(['accounts', 'codex', '--', '--version'], {
    extraEnv: { PDD_E2E_CODEX_LOG: codexLog },
  });
  assert.equal(res.code, 0, res.stderr);
  assert.ok(existsSync(codexLog), 'accounts codex must invoke the codex binary');
  assert.deepEqual(JSON.parse(readFileSync(codexLog, 'utf8').trim()).args, ['--version']);
  assert.match(
    res.stdout,
    /codex-cli 0\.99\.0-e2e/,
    'non-TTY pdd accounts codex dropped child stdout (src/accounts-cli.mjs:runPlainCodexOnce)',
  );
});

test('all 3 product commands work end-to-end on real coffee-pickup product fixture', async () => {
  const fx = makeIsolatedFixture('product', PRODUCT_TEMPLATE);
  const ghEnv = { PDD_E2E_FAKE_GH: 'ok', PDD_E2E_REPO: 'example/coffee' };

  const statusJson = await fx.cli(['product', 'status', '--json'], { extraEnv: ghEnv });
  assert.equal(statusJson.code, 0, statusJson.stderr);
  const parsed = JSON.parse(statusJson.stdout);
  assert.ok(parsed && typeof parsed === 'object');
  const statusText = await fx.cli(['product', 'status'], { extraEnv: ghEnv });
  assert.equal(statusText.code, 0, statusText.stderr);
  assert.match(statusText.stdout, /coffee|part|slice|run/i);
  markExecuted('product.status');

  const nextRes = await fx.cli(['product', 'next'], { extraEnv: ghEnv });
  assert.equal(nextRes.code, 0, nextRes.stderr);
  const runMatch = /pdd product start\s+([A-Za-z0-9._-]+)/.exec(nextRes.stdout);
  assert.ok(runMatch, `product next should print a start command:\n${nextRes.stdout}`);
  markExecuted('product.next');

  const startRes = await fx.cli(['product', 'start', runMatch[1], '--no-run', '--agent', 'codex'], {
    extraEnv: ghEnv,
  });
  assert.equal(startRes.code, 0, `product start --no-run failed: ${startRes.stderr}\n${startRes.stdout}`);
  assert.match(startRes.stdout, /91|issue/i);
  markExecuted('product.start');

  // Product-mode flags on pdd test (--journeys, --app-map) and pdd simulate (--product)
  const journeysPreview = await fx.cli(['test', '--journeys', '--files', '--json']);
  assert.equal(journeysPreview.code, 2, journeysPreview.stderr);
  assert.match(journeysPreview.stderr, /No root product journeys found/);

  const appMapPreview = await fx.cli(['test', '--files', '--app-map', 'app/maps/phone.json']);
  assert.notEqual(appMapPreview.code, 3, appMapPreview.stderr);
  assert.doesNotMatch(appMapPreview.stderr, /ReferenceError|TypeError|SyntaxError/);

  const simProduct = await fx.cli(['simulate', '--product', '--no-open', '--no-wait']);
  assert.doesNotMatch(simProduct.stderr, /Unsupported command or options|ReferenceError|TypeError|SyntaxError/);
  assert.match(simProduct.stderr, /No tests found/);
});

test('graph and dependencies commands execute end-to-end safely offline', async () => {
  const fx = makeIsolatedFixture('graph-deps');

  // pdd graph offline (no saved graph -> clean summary, exit 0; never opens a browser)
  const graphEmpty = await fx.cli(['graph', '--repo', 'example/cli-fixture']);
  assert.equal(graphEmpty.code, 0, graphEmpty.stderr);
  assert.match(graphEmpty.stdout, /Repository: example\/cli-fixture/);
  assert.match(graphEmpty.stdout, /offline/);
  assert.match(graphEmpty.stdout, /Review: 0 current/);

  // Seed a cached graph in temp HOME and query a specific --issue
  const cachedGraphPath = join(fx.home, '.cache', 'pdd', 'graph', 'example', 'cli-fixture.json');
  mkdirSync(dirname(cachedGraphPath), { recursive: true });
  writeFileSync(
    cachedGraphPath,
    JSON.stringify({
      lastSync: '2026-11-18T12:00:00Z',
      graph: {
        repository: 'example/cli-fixture',
        capturedAt: '2026-11-18T12:00:00Z',
        nodes: [
          {
            key: 'https://github.com/example/cli-fixture/issues/1',
            title: 'Root E2E issue',
            dependencyState: 'ready',
            reviewState: 'current',
            executionState: 'idle',
            eligible: true,
            reasons: [],
            blockers: [],
            facts: [],
          },
        ],
        edges: [],
      },
    }),
  );
  const graphSeeded = await fx.cli(['graph', '--repo', 'example/cli-fixture', '--issue', '1']);
  assert.equal(graphSeeded.code, 0, graphSeeded.stderr);
  assert.match(graphSeeded.stdout, /Root E2E issue/);
  assert.match(graphSeeded.stdout, /no recorded open blocker/);
  markExecuted('graph');

  const apGraphSeeded = await fx.cli(['autopilot', 'graph', '--repo', 'example/cli-fixture', '--issue', '1']);
  assert.equal(apGraphSeeded.code, 0, apGraphSeeded.stderr);
  assert.match(apGraphSeeded.stdout, /Root E2E issue/);
  markExecuted('autopilot.graph');
});

test('all 19 autopilot commands execute end-to-end safely in isolated temp HOME and repo', async () => {
  const fx = makeIsolatedFixture('autopilot');
  const ghEnv = { PDD_E2E_FAKE_GH: 'ok', PDD_E2E_REPO: 'example/cli-fixture' };

  // 1. autopilot doctor (read-only checks with safe shims)
  const doctorRes = await fx.cli(['autopilot', 'doctor'], { extraEnv: ghEnv });
  const doctorOut = `${doctorRes.stdout}\n${doctorRes.stderr}`;
  assert.match(doctorOut, /\b(?:PASS|WARN|FAIL)\b/);
  assert.doesNotMatch(doctorOut, /ReferenceError|TypeError|SyntaxError/);
  markExecuted('autopilot.doctor');

  // 2-6. autopilot observe / auto / off / trust / untrust (writes pdd.json locally, exits 0 even offline)
  for (const [routeId, mode] of [
    ['autopilot.observe', 'observe'],
    ['autopilot.auto', 'auto'],
    ['autopilot.off', 'off'],
  ]) {
    const res = await fx.cli(['autopilot', mode]);
    assert.equal(res.code, 0, `autopilot ${mode} failed: ${res.stderr}`);
    assert.equal(JSON.parse(readFileSync(join(fx.repo, 'pdd.json'), 'utf8')).autopilot.mode, mode);
    markExecuted(routeId);
  }

  const trustRes = await fx.cli(['autopilot', 'trust', 'alice', 'bob']);
  assert.equal(trustRes.code, 0, trustRes.stderr);
  assert.deepEqual(JSON.parse(readFileSync(join(fx.repo, 'pdd.json'), 'utf8')).autopilot.trust, ['alice', 'bob']);
  markExecuted('autopilot.trust');

  const untrustRes = await fx.cli(['autopilot', 'untrust', 'alice']);
  assert.equal(untrustRes.code, 0, untrustRes.stderr);
  assert.deepEqual(JSON.parse(readFileSync(join(fx.repo, 'pdd.json'), 'utf8')).autopilot.trust, ['bob']);
  markExecuted('autopilot.untrust');

  // 7. autopilot status (default, --all, --json)
  const apStatus = await fx.cli(['autopilot', 'status']);
  assert.equal(apStatus.code, 0, apStatus.stderr);
  assert.match(apStatus.stdout, /Autopilot disabled/);
  const apStatusAll = await fx.cli(['autopilot', 'status', '--all']);
  assert.equal(apStatusAll.code, 0, apStatusAll.stderr);
  const apStatusJson = await fx.cli(['autopilot', 'status', '--json']);
  assert.equal(apStatusJson.code, 0, apStatusJson.stderr);
  assert.doesNotThrow(() => JSON.parse(apStatusJson.stdout));
  markExecuted('autopilot.status');

  // 8. autopilot logs (list, --json, --lines, --issue)
  const logsText = await fx.cli(['autopilot', 'logs']);
  assert.equal(logsText.code, 0, logsText.stderr);
  const logsJson = await fx.cli(['autopilot', 'logs', '--json', '--lines', '25']);
  assert.equal(logsJson.code, 0, logsJson.stderr);
  assert.doesNotThrow(() => JSON.parse(logsJson.stdout));
  const logsIssue = await fx.cli(['autopilot', 'logs', '--issue', '42', '--json']);
  assert.doesNotMatch(logsIssue.stderr, /ReferenceError|TypeError|SyntaxError/);
  markExecuted('autopilot.logs');

  // 9. autopilot start (cleanly refuses missing label for observe mode, and exercises flags safely)
  const startNoLabel = await fx.cli(['autopilot', 'start', '--mode', 'observe'], { extraEnv: ghEnv });
  assert.equal(startNoLabel.code, 1);
  assert.match(startNoLabel.stderr, /label/i);
  const startFullEngine = await fx.cli(['autopilot', 'start', '--engine', 'full'], { extraEnv: ghEnv });
  assert.equal(startFullEngine.code, 2);
  const startBadIssues = await fx.cli(['autopilot', 'start', '--issues', 'abc'], { extraEnv: ghEnv });
  assert.equal(startBadIssues.code, 2);
  markExecuted('autopilot.start');

  // 9b. autopilot suite (direct queue-backed suite without workflow dependencies)
  const suiteMissingCmd = await fx.cli(['autopilot', 'suite']);
  assert.equal(suiteMissingCmd.code, 2);
  await configureCheckCapacity({
    env: { PDD_SUITE_QUEUE: join(fx.home, '.local', 'state', 'pdd-suite-queue') },
    checks: 1,
    runs: 2,
    resources: {
      memory: { available: 16 * 1024 ** 3 },
      load: 0,
      check: { cpuIds: [0, 1, 2, 3], platform: 'other', battery: false, virtualized: true, taskset: null },
    },
  });
  const suitePass = await fx.cli(['autopilot', 'suite', '--command', "node -e 'console.log(\"autopilot-suite-ok\")'", '--timeout', '1']);
  assert.equal(suitePass.code, 0, suitePass.stderr);
  assert.match(suitePass.stdout, /autopilot-suite-ok|passed|completed|finished/i);
  markExecuted('autopilot.suite');

  // 10. autopilot stop (safe with launchctl/systemctl shims)
  const stopRes = await fx.cli(['autopilot', 'stop']);
  assert.equal(stopRes.code, 0, stopRes.stderr);
  assert.match(stopRes.stdout, /Autopilot stopped/);
  markExecuted('autopilot.stop');

  // 11-12. autopilot add & release (with safe fake gh shim)
  const addIssue = await fx.cli(['autopilot', 'add', '42'], { extraEnv: ghEnv });
  assert.equal(addIssue.code, 0, `autopilot add failed: ${addIssue.stderr}\n${addIssue.stdout}`);
  assert.match(addIssue.stdout, /Marked 1 issue\(s\) with pdd:autopilot/);
  markExecuted('autopilot.add');

  const releaseIssue = await fx.cli(['autopilot', 'release', '42'], { extraEnv: ghEnv });
  assert.notEqual(releaseIssue.code, 2, releaseIssue.stderr);
  assert.doesNotMatch(releaseIssue.stderr, /ReferenceError|TypeError|SyntaxError/);
  markExecuted('autopilot.release');

  // 13. autopilot intake [--json] (100% local)
  const intakeText = await fx.cli(['autopilot', 'intake']);
  assert.equal(intakeText.code, 0, intakeText.stderr);
  assert.match(intakeText.stdout, /Intake:/);
  const intakeJson = await fx.cli(['autopilot', 'intake', '--json']);
  assert.equal(intakeJson.code, 0, intakeJson.stderr);
  assert.equal(JSON.parse(intakeJson.stdout).intake, 'off');
  markExecuted('autopilot.intake');

  // 14. autopilot report (list + send missing fingerprint)
  const reportList = await fx.cli(['autopilot', 'report']);
  assert.equal(reportList.code, 0, reportList.stderr);
  assert.match(reportList.stdout, /No local Autopilot report drafts/);
  const reportSend = await fx.cli(['autopilot', 'report', 'send', 'deadbeef']);
  assert.notEqual(reportSend.code, 0);
  assert.notEqual(reportSend.code, 2, reportSend.stderr);
  markExecuted('autopilot.report');

  // 15. autopilot regressions (--json and --file)
  const regFile = join(fx.dir, 'regressions-report.md');
  const regRes = await fx.cli(['autopilot', 'regressions', '--json', '--file', regFile], { extraEnv: ghEnv });
  assert.notEqual(regRes.code, 2, regRes.stderr);
  assert.doesNotMatch(regRes.stderr, /ReferenceError|TypeError|SyntaxError/);
  markExecuted('autopilot.regressions');

  // 16. autopilot alerts (set webhook -> verify secret redacted & 0600 -> clear -> test)
  const fakeWebhook = 'https://discord.com/api/webhooks/123456789012345678/e2e_secret_token_value';
  const alertSet = await fx.cli(['autopilot', 'alerts', 'set', '--destination', 'autopilot'], {
    stdin: `${fakeWebhook}\n`,
  });
  assert.equal(alertSet.code, 0, alertSet.stderr);
  assert.doesNotMatch(`${alertSet.stdout}\n${alertSet.stderr}`, /e2e_secret_token_value/);
  const savedAlertCfg = join(fx.home, '.config', 'pdd', 'autopilot-alerts.json');
  assert.ok(existsSync(savedAlertCfg), 'alerts config must be saved in temp HOME');
  assert.equal(statSync(savedAlertCfg).mode & 0o077, 0, 'alerts config must be owner-only (0600)');

  const botStdinSet = await fx.cli(
    ['autopilot', 'alerts', 'set', '--discord-channel', '123456789012345678', '--destination', 'infrastructure'],
    { stdin: 'e2e_synthetic_discord_bot_token_12345\n' },
  );
  assert.equal(botStdinSet.code, 0, botStdinSet.stderr);
  assert.doesNotMatch(`${botStdinSet.stdout}\n${botStdinSet.stderr}`, /e2e_synthetic_discord_bot_token_12345/);

  // --token-command performs live Discord API verification, so offline network guard fails cleanly with exit 1
  const botCmdOffline = await fx.cli([
    'autopilot', 'alerts', 'set',
    '--discord-channel', '123456789012345678',
    '--token-command', 'echo e2e_synthetic_discord_bot_token_12345',
    '--destination', 'infrastructure',
  ]);
  assert.equal(botCmdOffline.code, 1, botCmdOffline.stderr);
  assert.match(`${botCmdOffline.stdout}\n${botCmdOffline.stderr}`, /Discord bot check failed/);

  const alertClear = await fx.cli(['autopilot', 'alerts', 'clear', '--destination', 'autopilot']);
  assert.equal(alertClear.code, 0, alertClear.stderr);
  assert.equal(existsSync(savedAlertCfg), false);

  const alertTestNoDest = await fx.cli(['autopilot', 'alerts', 'test', '--destination', 'autopilot']);
  assert.notEqual(alertTestNoDest.code, 0);
  assert.notEqual(alertTestNoDest.code, 2, alertTestNoDest.stderr);
  markExecuted('autopilot.alerts');

  // 17. autopilot alert (records local incident in temp HOME when no webhook configured)
  const sendAlert = await fx.cli(
    ['autopilot', 'alert', '--issue', '42', '--kind', 'stuck', '--input', '-'],
    {
      stdin: JSON.stringify({ cause: 'Fixture blocked', tried: 'Local check', need: 'Human review' }),
      extraEnv: ghEnv,
    },
  );
  assert.equal(sendAlert.code, 0, `autopilot alert failed: ${sendAlert.stderr}\n${sendAlert.stdout}`);
  const updateAlert = await fx.cli(
    ['autopilot', 'alert', '--issue', '42', '--kind', 'stuck', '--update', '--input', '-'],
    {
      stdin: JSON.stringify({ cause: 'Fixture still blocked', tried: 'Retried locally', need: 'Human review' }),
      extraEnv: ghEnv,
    },
  );
  assert.equal(updateAlert.code, 0, `autopilot alert --update failed: ${updateAlert.stderr}\n${updateAlert.stdout}`);
  markExecuted('autopilot.alert');

  const checkBaseRes = await fx.cli(['autopilot', 'check-base', '999', '55'], { extraEnv: ghEnv });
  assert.equal(checkBaseRes.code, 1);
  assert.doesNotMatch(checkBaseRes.stderr, /ReferenceError|TypeError|SyntaxError/);
  markExecuted('autopilot.check-base');
});

test('all 6 metrics commands and major flags work end-to-end offline', async () => {
  const fx = makeIsolatedFixture('metrics');

  // metrics on & off (--json and --repo)
  const offRes = await fx.cli(['metrics', 'off', '--repo', 'example/cli-fixture', '--json']);
  assert.equal(offRes.code, 0, offRes.stderr);
  assert.equal(JSON.parse(offRes.stdout).enabled, false);
  markExecuted('metrics.off');

  const onRes = await fx.cli(['metrics', 'on', '--repo', 'example/cli-fixture', '--json']);
  assert.equal(onRes.code, 0, onRes.stderr);
  assert.equal(JSON.parse(onRes.stdout).enabled, true);
  markExecuted('metrics.on');

  // overview, stages, skills, full: text, --json, --date, --timezone, --html --file
  const views = [
    { id: 'metrics', args: [], supportsRepos: true },
    { id: 'metrics.stages', args: ['stages'], supportsRepos: false },
    { id: 'metrics.skills', args: ['skills'], supportsRepos: false },
    { id: 'metrics.full', args: ['full'], supportsRepos: true },
  ];
  for (const view of views) {
    const textRes = await fx.cli(['metrics', ...view.args]);
    assert.equal(textRes.code, 0, `${view.id} text: ${textRes.stderr}`);
    assert.ok(textRes.stdout.trim().length > 0);

    const jsonArgs = [
      'metrics', ...view.args,
      ...(view.supportsRepos ? ['--repos'] : []),
      '--repo', 'example/cli-fixture',
      '--date', '2026-11-18',
      '--timezone', 'UTC',
      '--json',
    ];
    const jsonRes = await fx.cli(jsonArgs);
    assert.equal(jsonRes.code, 0, `${view.id} json: ${jsonRes.stderr}`);
    const data = JSON.parse(jsonRes.stdout);
    assert.ok(data && typeof data === 'object');

    const htmlPath = join(fx.dir, `${view.id}.html`);
    const htmlRes = await fx.cli(['metrics', ...view.args, '--html', '--file', htmlPath]);
    assert.equal(htmlRes.code, 0, `${view.id} html: ${htmlRes.stderr}`);
    assert.ok(existsSync(htmlPath), `${view.id} must write HTML report`);
    assert.match(readFileSync(htmlPath, 'utf8'), /<!doctype html>|<html/i);
    markExecuted(view.id);
  }
});

test('removed commands, quiet aliases, and invalid flag/operand errors return exit code 2 cleanly', async () => {
  const fx = makeIsolatedFixture('errors');

  const cases = [
    // Removed commands name the replacement command
    { args: ['check'], match: /was removed.*Use pdd test/ },
    { args: ['check', '--lint'], match: /was removed.*Use pdd lint/ },
    { args: ['try'], match: /was removed.*Use pdd simulate/ },
    { args: ['help', 'check'], match: /was removed.*Use pdd test/ },
    // Unknown commands & unknown/duplicate flags
    { args: ['not-a-real-command'], match: /Unknown command "not-a-real-command"/ },
    { args: ['--no-such-flag'], match: /Unsupported command or options/ },
    { args: ['setup', '--no-such-flag'], match: /Unsupported command or options/ },
    { args: ['files', '--json', '--json'], match: /Unsupported command or options/ },
    // Invalid bounds & choices
    { args: ['test', '--timeout', '0'], match: /Unsupported command or options/ },
    { args: ['test', '--timeout', '999'], match: /Unsupported command or options/ },
    { args: ['test', '--target', 'bogus'], match: /Unsupported command or options/ },
    { args: ['completion', 'fish'], match: /Unsupported command or options/ },
    // Missing operands & retired workflow command
    { args: ['owner'], match: /Unsupported command or options/ },
    { args: ['workflow', 'list'], match: /pdd workflow was removed[\s\S]*\/pdd[\s\S]*pdd prove[\s\S]*pdd autopilot/ },
    // Cross-flag semantic validation (exit 2)
    { args: ['test', '--target', 'code', '--timeout', '5'], match: /accepts only --json/ },
    { args: ['metrics', '--json', '--html'], match: /either --json or --html/ },
    { args: ['metrics', '--file', 'out.html'], match: /requires "--html"/ },
    { args: ['autopilot', 'logs', '--follow', '--json'], match: /cannot be combined with --follow/ },
    { args: ['autopilot', 'logs', '--follow'], match: /Select an issue to follow/ },
    { args: ['autopilot', 'logs', 'not-an-issue'], match: /valid issue number/ },
    { args: ['autopilot', 'alert', '--issue', '42', '--kind', 'stuck'], match: /--input -/ },
    { args: ['autopilot', 'alerts', 'clear', '--discord-channel', '123456789012345678'], match: /only with pdd autopilot alerts set/ },
    { args: ['lint', '--local', '--remote'], match: /either --local or --remote/ },
    { args: ['accounts', 'share', 'e2e-primary', '--all', '--with', 'alice'], match: /either LABEL or --all/ },
    { args: ['accounts', 'add', '--provider', 'claude', '--device-auth'], match: /only supported for Codex/ },
    { args: ['accounts', 'add', '--loop'], match: /interactive terminal/ },
  ];

  const results = await runPool(cases, 8, async item => ({ item, res: await fx.cli(item.args) }));
  for (const { item, res } of results) {
    assert.equal(res.code, 2, `pdd ${item.args.join(' ')} expected exit 2, got ${res.code}\nstdout: ${res.stdout}\nstderr: ${res.stderr}`);
    assert.match(res.stderr, item.match, `pdd ${item.args.join(' ')} stderr mismatch: ${res.stderr}`);
  }

  // Quiet aliases parse and run like their canonical prefixes
  const quietSimHelp = await fx.cli(['sim', '--help']);
  assert.equal(quietSimHelp.code, 0, quietSimHelp.stderr);
  assert.match(quietSimHelp.stdout, /pdd simulate/);
});
});

test('runtime verification guard: every public command executed a real bin/pdd.mjs subprocess test', () => {
  const missing = PUBLIC_COMMAND_IDS.filter(id => !executedRoutes.has(id));
  assert.deepEqual(
    missing,
    [],
    `These public catalog commands were NOT executed end-to-end during this run: ${missing.join(', ')}`,
  );
});
