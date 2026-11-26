import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { mkdtemp, mkdir, writeFile, readFile, realpath, stat, symlink, link, rm } from 'node:fs/promises';
import { spawnSync, execFile } from 'node:child_process';
import { createServer } from 'node:http';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { createLiveLocalHost } from '../src/core/live-local-host.mjs';
import { rememberSecrets, redactSecrets, knownSecretValues } from '../src/secret-redaction.mjs';
import { parseArgv, CommandInputError } from '../src/argument-parser.mjs';
import { renderCompletion } from '../src/completion.mjs';
import { PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { compileLocalManifest, validateLocalManifest, validateLocalRequest, executeLocalCommand, check, simulate, runTry, proseSha256 } from '../src/runtime-seam.mjs';
import { evaluateValidationOutcome } from '../src/autopilot-validator.mjs';
import { harbor, fakeRuntime, portsFor, TOKEN } from './helpers/runtime-fake.mjs';

const execFileAsync = promisify(execFile);
const repoRoot = fileURLToPath(new URL('..', import.meta.url));
const pddBin = join(repoRoot, 'bin', 'pdd.mjs');
const redaction = { remember: rememberSecrets, redact: redactSecrets, known: knownSecretValues };

async function fixture(t) {
  const root = await mkdtemp(join(tmpdir(), 'pdd-local-host-'));
  t.after(() => rm(root, { recursive: true, force: true }));
  const bin = join(root, 'bin');
  await mkdir(bin);
  const env = { HOME: root, PATH: bin, PDD_STATE_DIR: join(root, 'state') };
  return { root, bin, env, host: createLiveLocalHost({ env, redaction }) };
}

const request = (argv, extra = {}) => ({
  argv,
  cwd: '.',
  stdin: '',
  timeout_ms: 1000,
  stdout_limit_bytes: 65536,
  stderr_limit_bytes: 65536,
  ...extra,
});

function createLiveLocalFakeServer(t, { kind = 'check', executedCommands = [], onCheckPost, onTryPost } = {}) {
  const registrations = new Map();
  let pendingPolls = 0;
  let replied = false;
  let tryReads = 0;
  return fakeRuntime(t, (entry, f) => {
    if (entry.url === '/v1/local-commands/registrations' && entry.method === 'POST') {
      const reg = {
        schema_version: entry.json.schema_version,
        capability: entry.json.capability,
        client_id: entry.json.client_id,
        registration_id: 'reg-live-1',
        epoch: 1,
      };
      registrations.set(reg.registration_id, reg);
      return { status: 200, json: reg };
    }
    if (entry.url.endsWith('/revoke') && entry.method === 'POST') {
      return { status: 200, json: { revoked: true } };
    }
    if (entry.url.endsWith('/connect') && entry.method === 'POST') {
      return {
        status: 200,
        json: {
          schema_version: entry.json.schema_version,
          capability: entry.json.capability,
          client_id: entry.json.client_id,
          epoch: 1,
        },
      };
    }
    if (entry.url.includes('/local-commands/pending?')) {
      pendingPolls++;
      if (!replied && pendingPolls === 1) {
        return { status: 200, json: { request_ids: ['cmd-req-1'] } };
      }
      return { status: 200, json: { request_ids: [] } };
    }
    if (entry.url.includes('/local-commands/cmd-req-1/events') && entry.method === 'POST') {
      const { action, request_id, result } = entry.json;
      if (action === 'poll') {
        return {
          status: 200,
          json: {
            request_id,
            state: 'claimed',
            dispatch_permitted: false,
            request: {
              schema_version: 'prompt-runtime.local-command-request.v1',
              request_id,
              run_id: entry.json.session_id,
              action_id: 'act-1',
              attempt_id: 'att-1',
              call_id: 'call-1',
              graph_id: 'g-1',
              edge_id: 'e-1',
              resource: 'tool',
              operation: 'read',
              binding_id: 'local-tool',
              access: 'read',
              argv: ['toolcmd', 'hello'],
              stdin: '',
              cwd: '.',
              environment: ['LOCAL_API_SECRET'],
              timeout_ms: 30000,
              stdout_limit_bytes: 16384,
              stderr_limit_bytes: 16384,
            },
            outcome: null,
            result: null,
          },
        };
      }
      if (action === 'started') {
        return {
          status: 200,
          json: { request_id, state: 'dispatched', dispatch_permitted: true, request: null, outcome: null, result: null },
        };
      }
      if (action === 'reply') {
        replied = true;
        executedCommands.push(result);
        return {
          status: 200,
          json: { request_id, state: 'completed', dispatch_permitted: false, request: null, outcome: null, result },
        };
      }
    }
    if (entry.method === 'POST' && entry.command === 'lint') {
      return { status: 200, json: f.lint(entry.request.requestId) };
    }
    if (entry.method === 'POST' && entry.command === 'check') {
      onCheckPost?.(entry.request);
      return { status: 202, json: f.check(entry.request.requestId, 'queued') };
    }
    if (entry.method === 'POST' && entry.command === 'try') {
      onTryPost?.(entry.request);
      return { status: 200, json: f.tryJob(entry.request.requestId, `${f.origin}/s/${'t'.repeat(43)}/`, 'running') };
    }
    if (entry.method === 'DELETE' && entry.url.startsWith('/v1/try/')) {
      return { status: 200, json: { stopped: true } };
    }
    if (entry.method === 'GET' && entry.url.startsWith('/v1/runs/')) {
      const id = entry.url.split('/').at(-1);
      if (kind === 'try') {
        tryReads++;
        const state = replied || tryReads >= 3 ? 'stopped' : 'running';
        return { status: 200, json: f.tryJob(id, `${f.origin}/s/${'t'.repeat(43)}/`, state) };
      }
      return { status: 200, json: f.check(id, replied ? 'passed' : 'running') };
    }
    return f.normal(entry);
  }).then(fake => {
    fake.capacity = () => ({
      status: 200,
      json: {
        features: ['owner-local-check-v1', 'owner-local-try-v1', 'private-live-reports-v1'],
      },
    });
    return fake;
  });
}

test('public --live-local, --command-manifest, and --allow-live-writes flags parse only on test and direct runs and appear in shell completion', () => {
  const testPlan = parseArgv(['test', 'story', '--live-local', '--command-manifest', '/private/commands.json', '--allow-live-writes']);
  assert.deepEqual(testPlan.options, { '--live-local': true, '--command-manifest': '/private/commands.json', '--allow-live-writes': true });
  assert.throws(() => parseArgv(['test', '--command-manifest']), CommandInputError);
  assert.throws(() => parseArgv(['test', '--command-manifest', '']), CommandInputError);
  assert.throws(() => parseArgv(['test', '--command-manifest', '   ']), CommandInputError);

  const directDotPlan = parseArgv(['.', '--live-local', '--command-manifest', '/private/commands.json', '--allow-live-writes']);
  assert.equal(directDotPlan.local, 'runtime-try');
  assert.deepEqual(directDotPlan.options, { '--live-local': true, '--command-manifest': '/private/commands.json', '--allow-live-writes': true });

  const directLeadingPlan = parseArgv(['--live-local', '--command-manifest', '/private/commands.json', '--allow-live-writes', 'story']);
  assert.equal(directLeadingPlan.local, 'runtime-try');
  assert.deepEqual(directLeadingPlan.operands, ['story']);
  assert.deepEqual(directLeadingPlan.options, { '--live-local': true, '--command-manifest': '/private/commands.json', '--allow-live-writes': true });

  const directTrailingPrompt = parseArgv(['prompts/app.prompt.md', '--live-local', '--command-manifest', '/private/commands.json']);
  assert.equal(directTrailingPrompt.local, 'runtime-try');
  assert.deepEqual(directTrailingPrompt.operands, ['prompts/app.prompt.md']);
  assert.deepEqual(directTrailingPrompt.options, { '--live-local': true, '--command-manifest': '/private/commands.json' });

  for (const flag of ['--live-local', '--command-manifest', '--allow-live-writes']) {
    assert.throws(() => parseArgv(['lint', flag, ...(flag === '--command-manifest' ? ['/tmp/c.json'] : [])]), CommandInputError);
    for (const shell of ['bash', 'zsh']) assert.ok(renderCompletion(shell).includes(flag), `${shell} completion includes ${flag}`);
    assert.equal(PUBLIC_COMMAND_ROUTES.filter(route => route.options.some(option => option.name === flag)).length, 2);
  }
  for (const retired of ['simulate', 'sim', 'try']) {
    assert.throws(() => parseArgv([retired, '--live-local', '--command-manifest', '/tmp/c.json']), CommandInputError);
  }
});

test('seam compiles concise command-map shorthand manifests read by the local host', async t => {
  const { root, host } = await fixture(t);
  const path = join(root, 'shorthand.json');
  await writeFile(path, JSON.stringify({
    commands: {
      'github.read': {
        cmd: ['gh', 'repo', 'view', '{repo}', '--json', 'name'],
        env: ['GH_TOKEN'],
      },
    },
    simulated_resources: ['clock'],
  }));
  const raw = await host.readManifest({ path, root });
  const compiled = compileLocalManifest(raw);
  assert.equal(compiled.schema_version, 'pdd.live-local-manifest.v1');
  assert.deepEqual(validateLocalManifest(compiled), compiled);
  assert.deepEqual(compiled.selection.resources, [
    { resource: 'github', mode: 'real', location: 'local', binding_id: 'local-github' },
    { resource: 'clock', mode: 'fake', location: 'simulation', binding_id: 'sim-clock' },
  ]);
  const wire = {
    schema_version: 'prompt-runtime.local-command-request.v1',
    request_id: 'req-1',
    run_id: 'run-1',
    action_id: 'act-1',
    attempt_id: 'att-1',
    call_id: 'call-1',
    graph_id: 'graph-1',
    edge_id: 'edge-1',
    resource: 'github',
    operation: 'read',
    binding_id: 'local-github',
    access: 'read',
    argv: ['gh', 'repo', 'view', 'promptdriven/pdd', '--json', 'name'],
    stdin: '',
    cwd: '.',
    environment: ['GH_TOKEN'],
    timeout_ms: 30000,
    stdout_limit_bytes: 16384,
    stderr_limit_bytes: 16384,
  };
  assert.deepEqual(validateLocalRequest(compiled, wire), wire);
});

test('manifest reader refuses nested and escaped duplicate keys, oversized manifests, and invalid UTF-8', async t => {
  const { root: parent, host } = await fixture(t);
  const root = join(parent, 'workspace');
  await mkdir(root);
  const path = join(parent, 'manifest.json');
  for (const content of ['{"x":1,"x":2}', '{"a":[{"x":1,"\\u0078":2}]}', '{', Buffer.from([0xff]), `{"pad":"${'a'.repeat(1024 * 1024 + 16)}"}`]) {
    await writeFile(path, content);
    await assert.rejects(host.readManifest({ path, root }), { code: 'live-local-manifest-invalid' });
  }
  await writeFile(path, '{"x":[{"a":1},{"a":2}],"text":"\\""}');
  assert.deepEqual(await host.readManifest({ path, root }), { x: [{ a: 1 }, { a: 2 }], text: '"' });
  const inside = join(root, 'manifest.json');
  await writeFile(inside, '{}');
  assert.deepEqual(await host.readManifest({ path: inside, root }), {});
  const linkPath = join(parent, 'link.json');
  await symlink(inside, linkPath);
  assert.deepEqual(await host.readManifest({ path: linkPath, root }), {});
  const frozen = await host.readManifest({ path, root });
  assert.equal(Object.isFrozen(frozen), true);
  assert.equal(Object.isFrozen(frozen.x[0]), true);
  assert.throws(() => { frozen.x[0].a = 99; }, TypeError);

  // POSIX FIFO must fail immediately without blocking (O_NONBLOCK).
  if (process.platform !== 'win32') {
    const fifo = join(parent, 'manifest.fifo');
    const mk = spawnSync('mkfifo', [fifo], { encoding: 'utf8' });
    assert.equal(mk.status, 0, mk.stderr);
    await assert.rejects(host.readManifest({ path: fifo, root }), { code: 'live-local-manifest-invalid' });
  }
});

test('manifest capture custody checks selected identity, symlinks, hardlinks, and later mutation', async t => {
  const { root, host } = await fixture(t);
  const path = join(root, 'manifest.json');
  await writeFile(path, '{}');
  await writeFile(join(root, 'ordinary.txt'), 'ordinary');
  await host.readManifest({ path, root });
  assert.equal(await host.manifestInSource({ path, root, files: ['ordinary.txt'] }), false);
  // Realpath vs symlinked root must resolve to the same snapshot key when given the same relative path.
  const rootAlias = join(root, '..', `alias-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`);
  await symlink(root, rootAlias);
  t.after(() => rm(rootAlias, { force: true }));
  await host.readManifest({ path: 'manifest.json', root: rootAlias });
  assert.equal(await host.manifestInSource({ path: 'manifest.json', root: await realpath(root), files: ['ordinary.txt'] }), false);
  assert.equal(await host.manifestInSource({ path: 'manifest.json', root: await realpath(root), files: ['manifest.json'] }), true);
  assert.equal(await host.manifestInSource({ path, root, files: ['manifest.json'] }), true);
  await symlink(path, join(root, 'alias.json'));
  assert.equal(await host.manifestInSource({ path, root, files: ['alias.json'] }), true);
  await link(path, join(root, 'hardlink.json'));
  await host.readManifest({ path, root });
  assert.equal(await host.manifestInSource({ path, root, files: ['hardlink.json'] }), true);
  await writeFile(path, '{"changed":true}');
  await assert.rejects(host.manifestInSource({ path, root, files: ['ordinary.txt'] }));
});

test('host resolves a fixed basename and executes literal argv/stdin under named environment', async t => {
  const { root, bin, env, host } = await fixture(t);
  const path = join(bin, 'fixture');
  await writeFile(path, '#!/bin/sh\nprintf "%s|%s|" "$1" "$OWNER_LABEL"\ncat\n', { mode: 0o700 });
  env.PATH = `${bin}:/usr/bin:/bin`;
  env.OWNER_LABEL = 'local-reference';
  const resolvedExecutable = await host.resolveExecutable({ executable: 'fixture' });
  assert.equal(resolvedExecutable, await realpath(path));
  await assert.rejects(host.resolveExecutable({ executable: '/bin/sh' }));
  const environment = host.environment({ names: ['OWNER_LABEL', 'PATH'] });
  assert.equal(environment.OWNER_LABEL, env.OWNER_LABEL);
  assert.equal(environment.HOME, root);
  assert.ok(knownSecretValues().includes(env.OWNER_LABEL));
  const outcome = await host.execute({
    request: request(['fixture', '$(touch forbidden)'], { stdin: 'literal input' }),
    resolvedExecutable,
    root,
    environment,
  });
  assert.equal(outcome.stdout, '$(touch forbidden)|[redacted]|literal input');
  assert.equal(outcome.exit_code, 0);
  assert.equal(outcome.timed_out, false);
  await assert.rejects(stat(join(root, 'forbidden')), { code: 'ENOENT' });
});

test('host redacts complete split output before byte limits and preserves UTF-8', async t => {
  const { root, bin, host } = await fixture(t);
  const path = join(bin, 'fixture');
  rememberSecrets('synthetic-owner-needle');
  await writeFile(path, '#!/bin/sh\nprintf synthetic-owner-\nsleep 0.03\nprintf needle\nprintf "éé" >&2\n', { mode: 0o700 });
  const outcome = await host.execute({
    request: request(['fixture'], { stdout_limit_bytes: 5, stderr_limit_bytes: 3 }),
    resolvedExecutable: path,
    root,
    environment: { PATH: '/usr/bin:/bin' },
  });
  assert.equal(outcome.stdout, '[reda');
  assert.equal(outcome.stderr, 'é');
  assert.equal(outcome.stdout_truncated, true);
  assert.equal(outcome.stderr_truncated, true);

  // Truncating across a redacted key=value or URL secret marker must remain a redaction fixed point
  // so host.journal.write preserves the verified outcome instead of dropping it as outcome-lost.
  await writeFile(
    path,
    '#!/bin/sh\nprintf "prefix token=supersecret1234567890\\n"\nprintf "https://example.test/?foo=1&token=supersecret1234567890\\n" >&2\n',
    { mode: 0o700 },
  );
  const straddled = await host.execute({
    request: request(['fixture'], { stdout_limit_bytes: 16, stderr_limit_bytes: 36 }),
    resolvedExecutable: path,
    root,
    environment: { PATH: '/usr/bin:/bin' },
  });
  assert.equal(straddled.stdout_truncated, true);
  assert.equal(straddled.stderr_truncated, true);
  assert.equal(straddled.stdout.includes('supersecret'), false);
  assert.equal(straddled.stderr.includes('supersecret'), false);
  assert.equal(host.redact({ text: straddled.stdout }).text, straddled.stdout);
  assert.equal(host.redact({ text: straddled.stderr }).text, straddled.stderr);
  assert.ok(Buffer.byteLength(straddled.stdout, 'utf8') <= 16);
  assert.ok(Buffer.byteLength(straddled.stderr, 'utf8') <= 36);
  const receiptKey = 'b'.repeat(64);
  await host.journal.write(receiptKey, { state: 'result', result: { status: 'completed', outcome: straddled } });
  const persisted = await host.journal.read(receiptKey);
  assert.equal(persisted.result.outcome.stdout, straddled.stdout);
  assert.equal(persisted.result.outcome.stderr, straddled.stderr);

  // Also verify full executeLocalCommand + journal.write pipeline delivers 'completed' (never 'outcome-lost').
  const miniManifest = compileLocalManifest({
    schema_version: 'pdd.live-local-manifest.v1',
    selection: {
      schema_version: 'prompt-runtime.resource-selection.v2',
      resources: [{ resource: 'tool', mode: 'real', location: 'local', binding_id: 'b1' }],
    },
    commands: [{
      binding_id: 'b1',
      resource: 'tool',
      operation: 'read',
      access: 'read',
      executable: 'fixture',
      argv: [],
      parameters: [],
      stdin: { literal: '' },
      cwd: '.',
      environment: [],
      timeout_ms: 5000,
      stdout_limit_bytes: 16,
      stderr_limit_bytes: 36,
    }],
  });
  let delivered = null;
  const execOut = await executeLocalCommand(
    {
      mode: 'live-local',
      manifest_json: JSON.stringify(miniManifest),
      request_json: JSON.stringify({
        schema_version: 'prompt-runtime.local-command-request.v1',
        request_id: 'req-trunc-1',
        run_id: 'run-1',
        action_id: 'act-1',
        attempt_id: 'att-1',
        call_id: 'call-1',
        graph_id: 'g-1',
        edge_id: 'e-1',
        resource: 'tool',
        operation: 'read',
        binding_id: 'b1',
        access: 'read',
        argv: ['fixture'],
        stdin: '',
        cwd: '.',
        environment: [],
        timeout_ms: 5000,
        stdout_limit_bytes: 16,
        stderr_limit_bytes: 36,
      }),
      allow_writes: false,
      terminal: false,
    },
    {
      runner: {
        execute: async ({ request_json }) => host.execute({
          request: JSON.parse(request_json),
          resolvedExecutable: path,
          root,
          environment: { PATH: '/usr/bin:/bin' },
        }),
      },
      redaction: { redact: host.redact },
      delivery: {
        reply: async ({ result_json }) => {
          delivered = JSON.parse(result_json);
          await host.journal.write('c'.repeat(64), { state: 'result', result: delivered });
          return { accepted: true };
        },
      },
    },
  );
  assert.equal(execOut.status, 'completed');
  assert.equal(delivered.status, 'completed');
  assert.equal(delivered.outcome.stdout_truncated, true);
  assert.equal(delivered.outcome.stderr_truncated, true);
});

test('host refuses cwd traversal, symlink escape, and invalid environment before launch', async t => {
  const { root, host } = await fixture(t);
  await symlink(tmpdir(), join(root, 'outside'));
  for (const cwd of ['..', '/tmp', 'outside', '..\\outside']) {
    await assert.rejects(host.execute({
      request: request(['true'], { cwd }),
      resolvedExecutable: '/usr/bin/true',
      root,
      environment: {},
    }));
  }
  // Missing, null, array, or NUL-containing environment must reject instead of inheriting process.env.
  for (const environment of [undefined, null, [], { BAD: 'a\0b' }, { 'A=B': '1' }]) {
    await assert.rejects(host.execute({
      request: request(['true']),
      resolvedExecutable: '/usr/bin/true',
      root,
      environment,
    }));
  }
});

test('host timeout and abort kill child groups and suppress >1 MiB overflow', async t => {
  const { root, bin, host } = await fixture(t);
  const path = join(bin, 'fixture');
  await writeFile(path, '#!/bin/sh\n(sleep 0.3; touch "$1") &\nwait\n', { mode: 0o700 });
  const marker = join(root, 'survived');
  const input = {
    request: request(['fixture', marker], { timeout_ms: 30 }),
    resolvedExecutable: path,
    root,
    environment: { PATH: '/usr/bin:/bin' },
  };
  const timeout = await host.execute(input);
  assert.equal(timeout.timed_out, true);
  assert.equal(timeout.exit_code, null);
  const controller = new AbortController();
  setTimeout(() => controller.abort(), 25);
  await assert.rejects(host.execute({ ...input, request: request(['fixture', marker]), signal: controller.signal }), { name: 'AbortError' });
  await host.sleep(400);
  await assert.rejects(stat(marker), { code: 'ENOENT' });
  await writeFile(path, '#!/bin/sh\n(sleep 0.2; touch "$1") &\nexit 0\n', { mode: 0o700 });
  const completed = await host.execute({ ...input, request: request(['fixture', marker]) });
  assert.equal(completed.exit_code, 0);
  await host.sleep(300);
  await assert.rejects(stat(marker), { code: 'ENOENT' });
  await writeFile(path, '#!/bin/sh\nyes x\n', { mode: 0o700 });
  await assert.rejects(host.execute({ ...input, request: request(['fixture']) }));
});

test('journal persists private 0600 atomic receipts, refuses unsafe paths and secret values', async t => {
  const { root, host } = await fixture(t);
  const key = 'a'.repeat(64);
  assert.equal(await host.journal.read(key), null);
  const value = { state: 'started', request_id: 'r1' };
  await host.journal.write(key, value);
  assert.deepEqual(await host.journal.read(key), value);
  const path = join(root, 'state', 'live-local-journal', `${key}.json`);
  assert.equal((await stat(path)).mode & 0o777, 0o600);
  assert.equal(await readFile(path, 'utf8'), JSON.stringify(value));
  await assert.rejects(host.journal.write('../escape', value));
  const inRoot = createLiveLocalHost({ env: { PDD_STATE_DIR: root }, redaction, root });
  await assert.rejects(inRoot.journal.write(key, value));
  rememberSecrets('journal-private-needle');
  await assert.rejects(host.journal.write(key, { stdout: 'journal-private-needle' }));
  await assert.rejects(host.journal.write(key, { token: 'unredacted-raw-value' }));
  await assert.rejects(host.journal.write(key, { stdout: 'secret=unredacted-value\n' }));
  // Already-redacted secret-labeled output must persist cleanly without false rejection on JSON quoting.
  const redactedReceipt = { state: 'result', outcome: { stdout: 'secret=[redacted]\nauthorization=[redacted]\n' } };
  await host.journal.write(key, redactedReceipt);
  assert.deepEqual(await host.journal.read(key), redactedReceipt);
  await rm(path);
  await symlink(join(root, 'target'), path);
  await assert.rejects(host.journal.write(key, value));
  await assert.rejects(host.journal.read(key));
  await rm(join(root, 'state', 'live-local-journal'), { recursive: true });
  await symlink(root, join(root, 'state', 'live-local-journal'));
  await assert.rejects(host.journal.write(key, value));
  await mkdir(join(root, 'real-state'), { mode: 0o700 });
  await symlink(join(root, 'real-state'), join(root, 'linked-state'));
  await assert.rejects(createLiveLocalHost({ env: { PDD_STATE_DIR: join(root, 'linked-state') }, redaction }).journal.write(key, value));
  await assert.rejects(createLiveLocalHost({ env: { PDD_STATE_DIR: join(root, 'linked-state', 'nested') }, redaction }).journal.write(key, value));
});

test('headless confirmation declines and sleep removes abort listener', async t => {
  const { host } = await fixture(t);
  if (!process.stdin.isTTY || !process.stdout.isTTY) {
    assert.equal(host.terminal, false);
    assert.deepEqual(await host.confirm({ binding_id: 'b', executable: 'fixture', argv: [] }), { confirmed: false });
  }
  const controller = new AbortController();
  const sleeping = host.sleep(10000, controller.signal);
  controller.abort();
  await assert.rejects(sleeping, { name: 'AbortError' });
});

test('public CLI refuses invalid --live-local combinations and incompatible test/direct flags with exit 2', async t => {
  const { root, env } = await fixture(t);
  const manifest = join(root, 'absent-owner-manifest.json');
  const exactCases = [
    [['test', '--allow-live-writes'], '--command-manifest and --allow-live-writes require --live-local.'],
    [['test', '--command-manifest', manifest], '--command-manifest and --allow-live-writes require --live-local.'],
    [['.', '--allow-live-writes'], '--command-manifest and --allow-live-writes require --live-local.'],
    [['.', '--command-manifest', manifest], '--command-manifest and --allow-live-writes require --live-local.'],
    [['test', '--live-local'], '--live-local requires an explicit --command-manifest path and Boolean write flag.'],
    [['.', '--live-local'], '--live-local requires an explicit --command-manifest path and Boolean write flag.'],
  ];
  for (const [argv, expected] of exactCases) {
    let stdout = '';
    let stderr = '';
    const code = await runPdd(argv, {
      cwd: root,
      env,
      stdout: { write: s => { stdout += s; } },
      stderr: { write: s => { stderr += s; } },
      syncOwnedUserSkills: () => ({ updated: [] }),
    });
    assert.equal(code, 2, `${argv.join(' ')}: ${stderr}`);
    assert.equal(stdout, '');
    assert.equal(stderr.trim(), expected, argv.join(' '));
  }

  const incompatibleCases = [
    ['test', '--live-local', '--command-manifest'],
    ['test', '--live-local', '--command-manifest', ''],
    ['test', '--live-local', '--command-manifest', '   '],
    ['.', '--live-local', '--command-manifest', '   '],
    ['test', '--live-local', '--command-manifest', manifest, '--lint'],
    ['test', '--live-local', '--command-manifest', manifest, '--codex'],
    ['test', '--live-local', '--command-manifest', manifest, '--local'],
    ['test', '--live-local', '--command-manifest', manifest, '--remote'],
    ['test', '--live-local', '--command-manifest', manifest, '--target', 'code'],
    ['test', '--live-local', '--command-manifest', manifest, '--read'],
    ['test', '--live-local', '--command-manifest', manifest, '--retry', 'batch-1'],
    ['test', '--live-local', '--command-manifest', manifest, '--reconcile', '11111111-1111-4111-8111-111111111111'],
    ['test', '--live-local', '--command-manifest', manifest, '--reconcile-stale'],
    ['test', '--live-local', '--command-manifest', manifest, '--files'],
    ['test', '--live-local', '--command-manifest', manifest, '--explain-bindings'],
    ['test', '--live-local', '--command-manifest', manifest, '--app-map', 'app-map.json'],
    ['test', '--live-local', '--command-manifest', manifest, '--screen', 'http://127.0.0.1:8080', '--drawing', 'a.ui.svg'],
    ['test', '--live-local', '--command-manifest', manifest, '--emit-v1'],
    ['test', '--live-local', '--command-manifest', manifest, '--write'],
    ['test', '--live-local', '--command-manifest', manifest, '--bind-criteria'],
    ['test', '--live-local', '--command-manifest', manifest, '--affected'],
    ['test', '--live-local', '--command-manifest', manifest, '--journeys'],
    ['test', '--live-local', '--command-manifest', manifest, '--lf'],
    ['test', '--live-local', '--command-manifest', manifest, '--cache-clear'],
    ['test', '--allow-live-writes', '--lint'],
    ['.', '--live-local', '--command-manifest', manifest, '--product'],
    ['.', '--live-local', '--command-manifest', manifest, '--parts', 'a'],
    ['.', '--live-local', '--command-manifest', manifest, '--journey', 'j'],
    ['.', '--live-local', '--command-manifest', manifest, '--stop'],
    ['.', '--live-local', '--command-manifest', manifest, '--save-last'],
    ['.', '--live-local', '--command-manifest', manifest, '--no-wait'],
    ['.', '--live-local', '--command-manifest', manifest, '--agent', 'codex'],
    ['.', '--live-local', '--command-manifest', manifest, '--cli'],
    ['.', '--live-local', '--command-manifest', manifest, '--shell'],
    ['.', '--live-local', '--command-manifest', manifest, '--serve'],
    ['.', '--live-local', '--command-manifest', manifest, '--data', 'state.json'],
    ['.', '--live-local', '--command-manifest', manifest, '--show-data'],
    ['.', '--live-local', '--command-manifest', manifest, '--quiet'],
    ['.', '--live-local', '--command-manifest', manifest, '-q'],
    ['prompts/place_order.prompt.md', '--live-local', '--command-manifest', manifest],
    ['app-map.json', '--live-local', '--command-manifest', manifest],
    ['lint', '--live-local', '--command-manifest', manifest],
    ['lint', '--allow-live-writes'],
  ];
  for (const argv of incompatibleCases) {
    let stdout = '';
    let stderr = '';
    const code = await runPdd(argv, {
      cwd: root,
      env,
      stdout: { write: s => { stdout += s; } },
      stderr: { write: s => { stderr += s; } },
      syncOwnedUserSkills: () => ({ updated: [] }),
    });
    assert.equal(code, 2, `${argv.join(' ')}: ${stderr}`);
    assert.equal(stdout, '');
    assert.ok(stderr.trim().length > 0, argv.join(' '));
    assert.doesNotMatch(stderr, /manifest-invalid|internal error|gh sign|not a git/i, argv.join(' '));
  }
});

test('runtime-seam wires --live-local host ports to @promptdriven/runtime-client and runs local command end-to-end', async t => {
  const setup = harbor(t);
  const bin = join(setup.sandbox, 'bin');
  mkdirSync(bin, { recursive: true });
  const toolBin = join(bin, 'toolcmd');
  writeFileSync(toolBin, '#!/bin/sh\nprintf "arg=%s secret=%s\\nauthorization: Bearer ghp_1234567890abcdef\\n" "$1" "$LOCAL_API_SECRET"\n', { mode: 0o755 });
  const manifestPath = join(setup.sandbox, 'commands.json');
  writeFileSync(manifestPath, JSON.stringify({
    schema_version: 'pdd.local-commands.v1',
    commands: {
      'tool.read': {
        cmd: ['toolcmd', '{arg}'],
        env: ['LOCAL_API_SECRET'],
      },
    },
  }));

  const executedCommands = [];
  let capturedCheckRequest = null;
  const fake = await createLiveLocalFakeServer(t, {
    kind: 'check',
    executedCommands,
    onCheckPost: req => { capturedCheckRequest = req; },
  });

  const env = {
    HOME: setup.home,
    PDD_RUNTIME_URL: fake.origin,
    PDD_STATE_DIR: setup.state,
    PATH: `${bin}:/usr/bin:/bin`,
    LOCAL_API_SECRET: 'super-secret-live-local-value-99',
  };
  const { ports } = portsFor(env);
  const code = await check(
    { words: ['place-order'], options: { '--live-local': true, '--command-manifest': manifestPath, '--json': true }, cwd: setup.repo },
    ports,
  );
  assert.equal(code, 0, ports.stderr.text);
  assert.equal(capturedCheckRequest?.resource_mode, 'live');
  assert.equal(capturedCheckRequest?.resource_setup?.registration_id, 'reg-live-1');
  assert.equal(executedCommands.length, 1);
  assert.equal(executedCommands[0].status, 'completed');
  assert.equal(executedCommands[0].outcome.exit_code, 0);
  assert.equal(executedCommands[0].outcome.stdout, 'arg=hello secret=[redacted]\nauthorization=[redacted]\n');

  // Real Git-tracked manifest inside captured repository source is refused with exit 2 before upload.
  const trackedSetup = harbor(t, repo => {
    writeFileSync(join(repo, 'prompts', 'commands.prompt.md'), JSON.stringify({
      schema_version: 'pdd.local-commands.v1',
      commands: { 'tool.read': { cmd: ['toolcmd', '{arg}'], env: ['LOCAL_API_SECRET'] } },
    }));
    const placePath = join(repo, 'prompts', 'place_order.prompt.md');
    const updated = readFileSync(placePath, 'utf8').replace('## Dependencies\n\nNone.', '## Dependencies\n\n- [commands](commands.prompt.md)');
    writeFileSync(placePath, updated.replace(/"prose_sha256":\s*"[a-f0-9]{64}"/, `"prose_sha256": "${proseSha256(updated)}"`));
  });
  const inSourceFake = await createLiveLocalFakeServer(t, { kind: 'check' });
  const { ports: inSourcePorts } = portsFor({ ...env, HOME: trackedSetup.home, PDD_STATE_DIR: trackedSetup.state, PDD_RUNTIME_URL: inSourceFake.origin });
  const inSourceCode = await check(
    { words: ['place-order'], options: { '--live-local': true, '--command-manifest': join(trackedSetup.repo, 'prompts', 'commands.prompt.md'), '--json': true }, cwd: trackedSetup.repo },
    inSourcePorts,
  );
  assert.equal(inSourceCode, 2);
  assert.match(inSourcePorts.stderr.text, /live-local-manifest-in-source/);

  // Relative --command-manifest path inside a repository subdirectory resolves against cwd cleanly.
  const subDir = join(setup.repo, 'sub');
  mkdirSync(subDir, { recursive: true });
  const subManifest = join(subDir, 'local-only.json');
  writeFileSync(subManifest, JSON.stringify({
    schema_version: 'pdd.local-commands.v1',
    commands: { 'tool.read': { cmd: ['toolcmd', '{arg}'], env: ['LOCAL_API_SECRET'] } },
  }));
  const subExecuted = [];
  const subFake = await createLiveLocalFakeServer(t, { kind: 'check', executedCommands: subExecuted });
  const { ports: subPorts } = portsFor({ ...env, PDD_RUNTIME_URL: subFake.origin });
  const subCode = await check(
    { words: ['place-order'], options: { '--live-local': true, '--command-manifest': './local-only.json', '--json': true }, cwd: subDir },
    subPorts,
  );
  assert.equal(subCode, 0, subPorts.stderr.text);
  assert.equal(subExecuted.length, 1);
  assert.equal(subExecuted[0].outcome.stdout, 'arg=hello secret=[redacted]\nauthorization=[redacted]\n');

  // runTry refuses standalone .prompt.md / app-map.json targets and --cli/--shell/--serve with --live-local.
  for (const [words, options] of [
    [['prompts/place_order.prompt.md'], { '--live-local': true, '--command-manifest': manifestPath }],
    [['app-map.json'], { '--live-local': true, '--command-manifest': manifestPath }],
    [['place-order'], { '--live-local': true, '--command-manifest': manifestPath, '--cli': true }],
    [['place-order'], { '--live-local': true, '--command-manifest': manifestPath, '--serve': '8080' }],
  ]) {
    const { ports: refusedTryPorts } = portsFor(env);
    const refusedTryCode = await runTry({ cwd: setup.repo, words, options }, refusedTryPorts);
    assert.equal(refusedTryCode, 2, `${words.join(' ')} ${JSON.stringify(options)}`);
  }

  // runTry injects default liveLocal host ports and forwards --live-local options directly.
  let seenTryInput = null;
  let seenTryPorts = null;
  const { ports: tryOverridePorts } = portsFor(env, {
    runTry: async (tryInput, tryPorts) => {
      seenTryInput = tryInput;
      seenTryPorts = tryPorts;
      return 0;
    },
  });
  const tryCode = await runTry(
    { cwd: setup.repo, words: ['place-order'], options: { '--live-local': true, '--command-manifest': manifestPath, '--allow-live-writes': true } },
    tryOverridePorts,
  );
  assert.equal(tryCode, 0);
  assert.equal(seenTryInput.options['--live-local'], true);
  assert.equal(seenTryInput.options['--command-manifest'], manifestPath);
  assert.equal(seenTryInput.options['--allow-live-writes'], true);
  assert.equal(typeof seenTryPorts.liveLocal?.execute, 'function');
  assert.equal(typeof seenTryPorts.liveLocal?.journal?.write, 'function');
});

test('real CLI subprocess invocation handles validation errors and live-local test/direct Story execution', async t => {
  // 1. Subprocess validation errors (exit 2)
  for (const [args, expected] of [
    [['test', '--allow-live-writes'], '--command-manifest and --allow-live-writes require --live-local.'],
    [['.', '--allow-live-writes'], '--command-manifest and --allow-live-writes require --live-local.'],
    [['test', '--live-local'], '--live-local requires an explicit --command-manifest path and Boolean write flag.'],
    [['.', '--live-local'], '--live-local requires an explicit --command-manifest path and Boolean write flag.'],
  ]) {
    const res = spawnSync(process.execPath, [pddBin, ...args], { encoding: 'utf8', timeout: 10000 });
    assert.equal(res.status, 2, `${args.join(' ')}: ${res.stderr}`);
    assert.equal(res.stdout, '');
    assert.equal(res.stderr.trim(), expected);
  }

  // 2. Real CLI subprocess `node bin/pdd.mjs test place-order --live-local --command-manifest <path> --json`
  const setup = harbor(t);
  const bin = join(setup.sandbox, 'bin');
  mkdirSync(bin, { recursive: true });
  writeFileSync(join(bin, 'gh'), `#!/bin/sh\nif [ "$1" = "auth" ]; then printf '%s\\n' '${TOKEN}'; exit 0; fi\nprintf 'octo 4242\\n'\n`, { mode: 0o755 });
  chmodSync(join(bin, 'gh'), 0o755);
  writeFileSync(join(bin, 'toolcmd'), '#!/bin/sh\nprintf "cli-sub=%s\\n" "$1"\n', { mode: 0o755 });
  chmodSync(join(bin, 'toolcmd'), 0o755);

  const manifestPath = join(setup.sandbox, 'sub-commands.json');
  writeFileSync(manifestPath, JSON.stringify({
    schema_version: 'pdd.local-commands.v1',
    commands: {
      'tool.read': { cmd: ['toolcmd', '{arg}'], env: ['LOCAL_API_SECRET'] },
    },
  }));

  const executedCheck = [];
  const checkFake = await createLiveLocalFakeServer(t, { kind: 'check', executedCommands: executedCheck });
  const env = {
    HOME: setup.home,
    PDD_RUNTIME_URL: checkFake.origin,
    PDD_STATE_DIR: setup.state,
    PATH: `${bin}:/usr/bin:/bin`,
    LOCAL_API_SECRET: 'cli-subprocess-secret',
  };
  const checkRes = await execFileAsync(
    process.execPath,
    [pddBin, 'test', 'place-order', '--live-local', '--command-manifest', manifestPath, '--json'],
    { cwd: setup.repo, env, timeout: 15000 },
  );
  assert.equal(executedCheck.length, 1, checkRes.stderr);
  assert.equal(executedCheck[0].outcome.stdout, 'cli-sub=hello\n');
  const parsedOut = JSON.parse(checkRes.stdout);
  assert.equal(parsedOut.exit_code, 0);
  assert.equal(parsedOut.rows[0].state, 'passed');

  // 3. Real CLI subprocess direct Story run `node bin/pdd.mjs place-order --live-local --command-manifest <path> --new --no-open`
  const executedTry = [];
  let tryReq = null;
  const tryFake = await createLiveLocalFakeServer(t, {
    kind: 'try',
    executedCommands: executedTry,
    onTryPost: req => { tryReq = req; },
  });
  const tryRes = await execFileAsync(
    process.execPath,
    [pddBin, 'place-order', '--live-local', '--command-manifest', manifestPath, '--new', '--no-open'],
    { cwd: setup.repo, env: { ...env, PDD_RUNTIME_URL: tryFake.origin }, timeout: 15000 },
  );
  assert.equal(tryReq?.resource_setup?.registration_id, 'reg-live-1', tryRes.stderr);
  assert.equal(executedTry.length, 1, tryRes.stderr);
  assert.equal(executedTry[0].outcome.stdout, 'cli-sub=hello\n');

  // 4. Regression: 0-Story, 1-prompt repo must fail closed on `pdd . --live-local` and bare `pdd --live-local`
  //    instead of falling through to simulated standalone runProgramTry with zero manifest checks.
  const soloRepo = join(setup.sandbox, 'solo-prompt-repo');
  mkdirSync(join(soloRepo, 'prompts'), { recursive: true });
  writeFileSync(join(soloRepo, 'prompts', 'solo.prompt.md'), '# Solo\nSay hi.\n');
  for (const args of [['init'], ['config', 'user.email', 't@example.com'], ['config', 'user.name', 'Test'], ['add', '.'], ['commit', '-m', 'init']]) {
    assert.equal(spawnSync('git', args, { cwd: soloRepo, encoding: 'utf8' }).status, 0);
  }
  let soloHits = 0;
  const soloGuard = createServer((_req, res) => {
    soloHits++;
    res.writeHead(500).end('unexpected network call');
  });
  await new Promise(resolve => soloGuard.listen(0, '127.0.0.1', resolve));
  t.after(() => new Promise(resolve => soloGuard.close(resolve)));
  const soloEnv = { ...env, PDD_RUNTIME_URL: `http://127.0.0.1:${soloGuard.address().port}` };
  for (const args of [
    ['.', '--live-local', '--command-manifest', '/does/not/exist/manifest.json', '--no-open'],
    ['--live-local', '--command-manifest', '/does/not/exist/manifest.json', '--no-open'],
  ]) {
    const res = spawnSync(process.execPath, [pddBin, ...args], { cwd: soloRepo, env: soloEnv, encoding: 'utf8', timeout: 10000 });
    assert.equal(res.status, 2, `${args.join(' ')}: ${res.stderr}`);
    assert.match(res.stderr, /--live-local applies to Story runs/);
  }
  assert.equal(soloHits, 0);
});

test('autopilot validator recognizes --live-local execution evidence', () => {
  const outcome = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/core/live-local-host.mjs'],
    nativeOnlyFiles: ['src/core/live-local-host.mjs'],
    offlinePassed: true,
    e2eChecks: [{
      kind: 'real-execution',
      command: 'pdd test my-story --live-local --command-manifest /tmp/commands.json',
      executed: true,
      exitCode: 0,
      passed: 1,
      failed: 0,
      skipped: 0,
    }],
  });
  assert.equal(outcome.eligible, true);
  assert.equal(outcome.decision, 'allow-merge');
});
