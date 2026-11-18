import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, writeFile, readFile, realpath, stat, symlink, link, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createLiveLocalHost } from '../src/live-local-host.mjs';
import { rememberSecrets, redactSecrets, knownSecretValues } from '../src/secret-redaction.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { renderCompletion } from '../src/completion.mjs';
import { PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { compileLocalManifest, validateLocalManifest, validateLocalRequest } from '../src/runtime-seam.mjs';

const redaction = { remember: rememberSecrets, redact: redactSecrets, known: knownSecretValues };
async function fixture(t) {
  const root = await mkdtemp(join(tmpdir(), 'pdd-local-host-'));
  t.after(() => rm(root, { recursive: true, force: true }));
  const bin = join(root, 'bin'); await mkdir(bin);
  const env = { HOME: root, PATH: bin, PDD_STATE_DIR: join(root, 'state') };
  return { root, bin, env, host: createLiveLocalHost({ env, redaction }) };
}
const request = (argv, extra = {}) => ({ argv, cwd: '.', stdin: '', timeout_ms: 1000, stdout_limit_bytes: 65536, stderr_limit_bytes: 65536, ...extra });

test('live-local flags parse only on test/simulate and appear in shell completion', () => {
  for (const command of ['test', 'simulate']) {
    const plan = parseArgv([command, 'story', '--live-local', '--command-manifest', '/private/manifest.json', '--allow-live-writes']);
    assert.deepEqual(plan.options, { '--live-local': true, '--command-manifest': '/private/manifest.json', '--allow-live-writes': true });
    assert.throws(() => parseArgv([command, '--command-manifest']));
  }
  for (const flag of ['--live-local', '--command-manifest', '--allow-live-writes']) {
    assert.throws(() => parseArgv(['lint', flag]));
    for (const shell of ['bash', 'zsh']) assert.ok(renderCompletion(shell).includes(flag));
    assert.equal(PUBLIC_COMMAND_ROUTES.filter(route => route.options.some(option => option.name === flag)).length, 2);
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

test('manifest reader refuses nested and escaped duplicate keys and invalid UTF-8', async t => {
  const { root: parent, host } = await fixture(t); const root = join(parent, 'workspace'); await mkdir(root); const path = join(parent, 'manifest.json');
  for (const content of ['{"x":1,"x":2}', '{"a":[{"x":1,"\\u0078":2}]}', '{', Buffer.from([0xff])]) {
    await writeFile(path, content);
    await assert.rejects(host.readManifest({ path, root }), { code: 'live-local-manifest-invalid' });
  }
  await writeFile(path, '{"x":[{"a":1},{"a":2}],"text":"\\\""}');
  assert.deepEqual(await host.readManifest({ path, root }), { x: [{ a: 1 }, { a: 2 }], text: '"' });
  const inside = join(root, 'manifest.json'); await writeFile(inside, '{}');
  assert.deepEqual(await host.readManifest({ path: inside, root }), {});
  const link = join(parent, 'link.json'); await symlink(inside, link);
  assert.deepEqual(await host.readManifest({ path: link, root }), {});
  const frozen = await host.readManifest({ path, root });
  assert.equal(Object.isFrozen(frozen), true); assert.equal(Object.isFrozen(frozen.x[0]), true);
  assert.throws(() => { frozen.x[0].a = 99; }, TypeError);
});

test('manifest capture custody checks selected identity and later mutation', async t => {
  const { root, host } = await fixture(t);
  const path = join(root, 'manifest.json'); await writeFile(path, '{}');
  await writeFile(join(root, 'ordinary.txt'), 'ordinary');
  await host.readManifest({ path, root });
  assert.equal(await host.manifestInSource({ path, root, files: ['ordinary.txt'] }), false);
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
  env.PATH = `${bin}:/usr/bin:/bin`; env.OWNER_LABEL = 'local-reference';
  const resolvedExecutable = await host.resolveExecutable({ executable: 'fixture' });
  assert.equal(resolvedExecutable, await realpath(path));
  await assert.rejects(host.resolveExecutable({ executable: '/bin/sh' }));
  const environment = host.environment({ names: ['OWNER_LABEL', 'PATH'] });
  assert.equal(environment.OWNER_LABEL, env.OWNER_LABEL);
  assert.equal(environment.HOME, root);
  assert.ok(knownSecretValues().includes(env.OWNER_LABEL));
  const outcome = await host.execute({ request: request(['fixture', '$(touch forbidden)'], { stdin: 'literal input' }), resolvedExecutable, root, environment });
  assert.equal(outcome.stdout, '$(touch forbidden)|[redacted]|literal input');
  assert.equal(outcome.exit_code, 0);
  assert.equal(outcome.timed_out, false);
  await assert.rejects(stat(join(root, 'forbidden')), { code: 'ENOENT' });
});

test('host redacts complete split output before byte limits and preserves UTF-8', async t => {
  const { root, bin, host } = await fixture(t); const path = join(bin, 'fixture');
  rememberSecrets('synthetic-owner-needle');
  await writeFile(path, '#!/bin/sh\nprintf synthetic-owner-\nsleep 0.03\nprintf needle\nprintf "éé" >&2\n', { mode: 0o700 });
  const outcome = await host.execute({ request: request(['fixture'], { stdout_limit_bytes: 5, stderr_limit_bytes: 3 }), resolvedExecutable: path, root, environment: { PATH: '/usr/bin:/bin' } });
  assert.equal(outcome.stdout, '[reda'); assert.equal(outcome.stderr, 'é');
  assert.equal(outcome.stdout_truncated, true); assert.equal(outcome.stderr_truncated, true);
});

test('host refuses cwd traversal and symlink escape before launch', async t => {
  const { root, host } = await fixture(t); await symlink(tmpdir(), join(root, 'outside'));
  for (const cwd of ['..', '/tmp', 'outside', '..\\outside']) await assert.rejects(host.execute({ request: request(['true'], { cwd }), resolvedExecutable: '/usr/bin/true', root, environment: {} }));
});

test('host timeout and abort kill child groups and suppress overflow', async t => {
  const { root, bin, host } = await fixture(t); const path = join(bin, 'fixture');
  await writeFile(path, '#!/bin/sh\n(sleep 0.3; touch "$1") &\nwait\n', { mode: 0o700 });
  const marker = join(root, 'survived');
  const input = { request: request(['fixture', marker], { timeout_ms: 30 }), resolvedExecutable: path, root, environment: { PATH: '/usr/bin:/bin' } };
  const timeout = await host.execute(input); assert.equal(timeout.timed_out, true); assert.equal(timeout.exit_code, null);
  const controller = new AbortController(); setTimeout(() => controller.abort(), 25);
  await assert.rejects(host.execute({ ...input, request: request(['fixture', marker]), signal: controller.signal }), { name: 'AbortError' });
  await host.sleep(400); await assert.rejects(stat(marker), { code: 'ENOENT' });
  await writeFile(path, '#!/bin/sh\n(sleep 0.2; touch \"$1\") &\nexit 0\n', { mode: 0o700 });
  const completed = await host.execute({ ...input, request: request(['fixture', marker]) });
  assert.equal(completed.exit_code, 0);
  await host.sleep(300); await assert.rejects(stat(marker), { code: 'ENOENT' });
  await writeFile(path, '#!/bin/sh\nyes x\n', { mode: 0o700 });
  await assert.rejects(host.execute({ ...input, request: request(['fixture']) }));
});

test('journal persists private atomic receipts, refuses unsafe paths and secret values', async t => {
  const { root, host } = await fixture(t); const key = 'a'.repeat(64);
  assert.equal(await host.journal.read(key), null);
  const value = { state: 'started', request_id: 'r1' };
  await host.journal.write(key, value); assert.deepEqual(await host.journal.read(key), value);
  const path = join(root, 'state', 'live-local-journal', `${key}.json`);
  assert.equal((await stat(path)).mode & 0o777, 0o600);
  assert.equal(await readFile(path, 'utf8'), JSON.stringify(value));
  await assert.rejects(host.journal.write('../escape', value));
  const inRoot = createLiveLocalHost({ env: { PDD_STATE_DIR: root }, redaction, root });
  await assert.rejects(inRoot.journal.write(key, value));
  rememberSecrets('journal-private-needle');
  await assert.rejects(host.journal.write(key, { stdout: 'journal-private-needle' }));
  await rm(path); await symlink(join(root, 'target'), path);
  await assert.rejects(host.journal.write(key, value)); await assert.rejects(host.journal.read(key));
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
  const controller = new AbortController(); const sleeping = host.sleep(10000, controller.signal); controller.abort();
  await assert.rejects(sleeping, { name: 'AbortError' });
});

test('public CLI refuses unsupported live options before manifest reads or hosted admission', async t => {
  const { runPdd } = await import('../src/pdd-cli.mjs');
  const { root, env } = await fixture(t);
  const manifest = join(root, 'absent-owner-manifest.json');
  const cases = [
    ['test', '--live-local', '--json'],
    ['test', '--command-manifest', manifest, '--json'],
    ['test', '--allow-live-writes', '--json'],
    ['test', '--live-local', '--command-manifest', manifest, '--files', '--json'],
    ['test', '--live-local', '--command-manifest', manifest, '--target', 'code', '--json'],
    ['test', '--live-local', '--command-manifest', manifest, '--read', '--json'],
    ['test', '--live-local', '--command-manifest', manifest, '--affected', '--json'],
    ['simulate', '--live-local', '--command-manifest', manifest, '--no-wait'],
    ['simulate', '--live-local', '--command-manifest', manifest, '--stop'],
    ['simulate', '--live-local', '--command-manifest', manifest, '--product'],
    ['lint', '--live-local'],
  ];
  for (const argv of cases) {
    let output = '';
    const sink = { write: text => { output += text; } };
    const code = await runPdd(argv, { cwd: root, env, stdout: sink, stderr: sink, syncOwnedUserSkills: () => ({ updated: [] }) });
    assert.equal(code, 2, `${argv.join(' ')}: ${output}`);
    assert.match(output, argv[0] === 'lint' ? /Unsupported command or options/ : /live-local|--target code/);
    assert.doesNotMatch(output, /manifest-invalid|internal error|gh sign|not a git/i);
  }
});
