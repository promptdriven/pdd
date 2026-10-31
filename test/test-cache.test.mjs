import test from 'node:test';
import * as disk from 'node:fs';
import { randomUUID } from 'node:crypto';
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import { chmodSync, existsSync, mkdirSync, readFileSync, readdirSync, unlinkSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { renderHelp } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { captureSource, interfaceBlocks, proseSha256 } from '../src/runtime-preflight.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

const vectors = JSON.parse(readFileSync(new URL('./runtime/test-cache.json', import.meta.url)));
const read = path => JSON.parse(readFileSync(path, 'utf8'));
const write = (path, value) => writeFileSync(path, JSON.stringify(value, null, 2) + '\n');
const git = (cwd, ...args) => spawnSync('git', args, { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
const checks = fake => fake.posts.filter(row => row.command === 'check');
function refresh(path) {
  let text = readFileSync(path, 'utf8').replace('"status": "approved"', '"status": "draft"');
  text = text.replace(/"prose_sha256"\s*:\s*"[a-f0-9]*"/, '"prose_sha256": "' + proseSha256(text) + '"');
  writeFileSync(path, text);
}
function independent(repo) {
  const story = readFileSync(join(repo, 'user_stories/place-order.md'), 'utf8');
  writeFileSync(join(repo, 'user_stories/independent.md'), story);
  writeFileSync(join(repo, 'prompts/independent.prompt.md'), readFileSync(join(repo, 'prompts/place_order.prompt.md')));
  const doc = read(join(repo, 'tests/place-order.json'));
  doc.story_path = 'user_stories/independent.md';
  for (const step of doc.steps) step.entry_path = 'prompts/independent.prompt.md';
  write(join(repo, 'tests/independent.json'), doc);
}
async function setup(t, edit) {
  const fixture = harbor(t, repo => { independent(repo); edit?.(repo); });
  let mode = 'passed';
  const fake = await fakeRuntime(t, entry => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: fake.lint(entry.request.requestId, ['prompts/place_order.prompt.md', 'prompts/independent.prompt.md'].map(path => ({ path, state: 'approved', admission_state: 'approved', interface: { calls: [] } }))) };
    if (mode === 'not_run') return { status: 503, json: { error: { code: 'pool-low-room', message: 'Not enough room for this check. Try again later.' } } };
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    return { status: 200, json: fake.check(id, mode) };
  });
  let requests = 0;
  const { ports, clock } = portsFor({ HOME: fixture.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: fixture.state }, {
    fetch: (...args) => { requests += 1; return globalThis.fetch(...args); }
  });
  const invoke = async (words = [], options = {}, cwd = fixture.repo) => {
    ports.stdout.text = ''; ports.stderr.text = '';
    const before = { posts: fake.posts.length, checks: checks(fake).length, requests, gh: clock.gh.length };
    const code = await runCheck({ words, options: { '--json': true, ...options }, cwd, cache: true }, ports);
    return { code, json: options['--json'] !== false && ports.stdout.text ? JSON.parse(ports.stdout.text) : null, err: ports.stderr.text,
      sent: checks(fake).length - before.checks, network: requests - before.requests, gh: clock.gh.length - before.gh };
  };
  return { ...fixture, fake, ports, clock, invoke, mode: value => { mode = value; } };
}
async function prime(ctx, verifyReuse = true) {
  const first = await ctx.invoke(); assert.equal(first.code, 0, first.err); assert.equal(first.sent, 3);
  if (!verifyReuse) return first;
  const repeat = await ctx.invoke();
  assert.equal(repeat.sent, 0, 'unchanged complete Story passes must be reused before dispatch');
  assert.equal(repeat.network, 0, 'reuse must not lint or read runtime'); assert.equal(repeat.gh, 0, 'reuse must not sign in');
  return repeat;
}

for (const vector of vectors.cases) test(`TEST-CACHE ${vector.id} (${vector.criterion_id})`, async t => {
  const id = vector.id;
  if (id === 'cli-options') {
    for (const command of ['test', 'check']) {
      let parsed, error;
      try { parsed = parseArgv([command, '--lf', '--cache-clear', 'tests']); } catch (caught) { error = caught; }
      assert.equal(error, undefined, 'test cache flags must parse on canonical and accepted former routes');
      assert.equal(parsed.options['--lf'], true); assert.equal(parsed.options['--cache-clear'], true);
    }
    return;
  }
  const ctx = await setup(t, repo => {
    if (id === 'call-target' || id === 'raw-hash') {
      const path = join(repo, 'prompts/place_order.prompt.md');
      const text = readFileSync(path, 'utf8'), block = interfaceBlocks(text)[0], doc = JSON.parse(block[1]);
      if (id === 'call-target') {
        writeFileSync(join(repo, 'prompts/helper.prompt.md'), text);
        doc.calls = [{ operation: 'helper', target: 'prompts/helper.prompt.md', target_operation: 'place_order', max_calls: 1 }];
      } else {
        mkdirSync(join(repo, 'contracts'));
        write(join(repo, 'contracts/input.json'), doc.entries[0].input_schema);
        doc.entries[0].input_schema = { $contract: 'contracts/input.json#' };
      }
      writeFileSync(path, text.slice(0, block.indices[1][0]) + JSON.stringify(doc) + text.slice(block.indices[1][1])); refresh(path);
    }
    if (id === 'transitive') {
      writeFileSync(join(repo, 'prompts/context.md'), 'Shared policy.\n');
      const path = join(repo, 'prompts/place_order.prompt.md');
      writeFileSync(path, readFileSync(path, 'utf8').replace('## Dependencies', '## Dependencies\n\n- [Policy](context.md): required runtime context.'));
      refresh(path);
    }
  });
  if (id === 'cli-reuse') {
    const bin = join(ctx.sandbox, 'bin'); mkdirSync(bin);
    const shim = join(bin, 'gh');
    writeFileSync(shim, '#!/bin/sh\nif [ "$1" = auth ]; then echo gho_TESTTOKEN_never_print_7f3a; else echo "octo 4242"; fi\n'); chmodSync(shim, 0o755);
    const cli = command => new Promise((resolve, reject) => {
      const child = spawn(process.execPath, [new URL('../bin/pdd.mjs', import.meta.url).pathname, command, '--json'], {
        cwd: ctx.repo, env: { ...process.env, HOME: ctx.home, PATH: `${bin}:${process.env.PATH}`, PDD_RUNTIME_URL: ctx.fake.origin, PDD_STATE_DIR: ctx.state }, stdio: ['ignore', 'pipe', 'pipe']
      });
      let out = '', err = ''; child.stdout.on('data', x => { out += x; }); child.stderr.on('data', x => { err += x; });
      child.on('error', reject); child.on('close', code => resolve({ code, out, err }));
    });
    const first = await cli('test'); assert.equal(first.code, 0, first.err);
    const before = checks(ctx.fake).length;
    const second = await cli('check'); assert.equal(second.code, 0, second.err);
    assert.equal(checks(ctx.fake).length, before, 'canonical test and former alias share normal CLI reuse');
    assert.ok(JSON.parse(second.out).rows.every(row => row.cached && row.calls === 0)); return;
  }
  const repeated = await prime(ctx, ['reuse', 'time-previous-day', 'mixed-json'].includes(id));
  if (id === 'call-target' || id === 'raw-hash') {
    const before = captureSource(ctx.repo).stories;
    if (id === 'call-target') {
      const path = join(ctx.repo, 'prompts/helper.prompt.md');
      writeFileSync(path, readFileSync(path, 'utf8').replace('Use this menu.', 'Use this menu carefully.')); refresh(path);
    } else {
      const path = join(ctx.repo, 'prompts/place_order.prompt.md');
      writeFileSync(path, readFileSync(path, 'utf8').replace('{"$contract":', '{  "$contract":'));
      assert.deepEqual(captureSource(ctx.repo).stories, before, 'reference-only formatting leaves effective footprint equal');
    }
    const result = await ctx.invoke(); assert.equal(result.sent, 2, 'changed reached/raw prompt reruns its two Stories');
    assert.equal(result.code, 0, result.err); return;
  }
  if (id === 'origin' || id === 'max-calls') {
    if (id === 'origin') {
      ctx.ports.env.PDD_RUNTIME_URL = ctx.fake.origin.replace('127.0.0.1', 'localhost');
      ctx.ports.fetch = (url, options) => globalThis.fetch(String(url).replace('localhost', '127.0.0.1'), options);
    }
    const result = await ctx.invoke([], id === 'max-calls' ? { '--max-calls': '50' } : {});
    assert.equal(result.sent, 3, 'changed execution origin or budget reruns every selected Story'); return;
  }
  if (id === 'reuse' || id === 'time-previous-day' || id === 'mixed-json') {
    assert.ok(repeated.json.rows.every(row => row.cached === true && row.calls === 0 && row.request_id === null && row.report_url === null));
    assert.match(repeated.json.summary_line, /3 Stories skipped/);
    if (id === 'time-previous-day') {
      ctx.clock.now += 86400000;
      const result = await ctx.invoke([], { '--json': false });
      assert.equal(result.sent, 0); assert.match(ctx.ports.stdout.text, /unchanged, passed 2026-10-27/);
    } else if (id === 'reuse') {
      await ctx.invoke([], { '--json': false });
      const at = new Date(ctx.clock.now); const time = `${String(at.getHours()).padStart(2, '0')}:${String(at.getMinutes()).padStart(2, '0')}`;
      assert.ok(ctx.ports.stdout.text.includes(`unchanged, passed ${time}`));
      assert.match(ctx.ports.stdout.text, /0 AI calls/);
    } else {
      const path = join(ctx.repo, 'tests/place-order.json'), doc = read(path); doc.initial_world.changed = true; write(path, doc);
      const result = await ctx.invoke(); assert.equal(result.sent, 1);
      assert.equal(result.json.rows.filter(row => row.cached).length, 2);
    }
    return;
  }
  if (['prompt', 'transitive', 'shared-data', 'test-data', 'story', 'unrelated'].includes(id)) {
    let expected = 1;
    if (id === 'prompt') {
      const path = join(ctx.repo, 'prompts/place_order.prompt.md'); writeFileSync(path, readFileSync(path, 'utf8').replace('Use this menu.', 'Use this menu carefully.')); refresh(path); expected = 2;
    } else if (id === 'transitive') { writeFileSync(join(ctx.repo, 'prompts/context.md'), 'Changed shared policy.\n'); expected = 2; }
    else if (id === 'shared-data') { writeFileSync(join(ctx.repo, 'shared.txt'), 'New shared seed.\n'); write(join(ctx.repo, 'pdd-source.json'), { include: ['shared.txt'] }); expected = 3; }
    else if (id === 'test-data') { const path = join(ctx.repo, 'tests/place-order.json'), doc = read(path); doc.initial_world.changed = true; write(path, doc); }
    else if (id === 'story') { const path = join(ctx.repo, 'user_stories/place-order.md'); writeFileSync(path, readFileSync(path, 'utf8') + '\nChanged explanation.\n'); }
    else { writeFileSync(join(ctx.repo, 'prompts/unrelated.prompt.md'), '# Unrelated\n'); expected = 0; }
    const result = await ctx.invoke(); assert.equal(result.sent, expected, 'only reaching Stories rerun'); assert.equal(result.code, 0, result.err);
    if (id === 'prompt') { const scoped = await ctx.invoke(['independent']); assert.equal(scoped.sent, 0); assert.equal(scoped.json.rows.length, 1); assert.equal(scoped.json.rows[0].cached, true); }
    return;
  }
  if (id === 'sibling') {
    const path = join(ctx.repo, 'tests/place-order-extra.json'); write(path, read(join(ctx.repo, 'tests/place-order.json')));
    assert.equal((await ctx.invoke(['tests/place-order.json'])).sent, 1);
    assert.equal((await ctx.invoke(['place-order'])).sent, 2, 'partial sibling pass cannot cache complete Story');
    assert.equal((await ctx.invoke(['place-order'])).sent, 0); return;
  }
  if (id === 'interrupted') {
    const path = join(ctx.repo, 'tests/place-order.json'), original = readFileSync(path, 'utf8'), doc = read(path);
    doc.initial_world.changed = true; write(path, doc);
    const sleep = ctx.ports.sleep; ctx.mode('running');
    ctx.ports.sleep = async ms => { ctx.clock.now += ms; ctx.clock.interrupt(); };
    const result = await ctx.invoke(['place-order']); assert.equal(result.code, 3);
    ctx.ports.sleep = sleep; ctx.mode('passed'); writeFileSync(path, original);
    assert.equal((await ctx.invoke(['place-order'])).sent, 1, 'interrupted attempt invalidates an older pass'); return;
  }
  if (['failed', 'refused', 'not_run', 'unknown', 'old-pass-invalidated'].includes(id)) {
    const path = join(ctx.repo, 'tests/place-order.json'), doc = read(path); doc.initial_world.changed = true; write(path, doc);
    ctx.mode(id === 'old-pass-invalidated' ? 'unknown' : id);
    const attempt = await ctx.invoke(['place-order']); assert.notEqual(attempt.code, 0);
    assert.equal(attempt.json.rows[0].state, id === 'old-pass-invalidated' ? 'unknown' : id);
    if (id === 'old-pass-invalidated') { delete doc.initial_world.changed; write(path, doc); }
    ctx.mode('passed'); assert.equal((await ctx.invoke(['place-order'])).sent, 1, 'nonpass invalidates older pass'); return;
  }
  if (id === 'lf' || id === 'lf-empty' || id === 'lf-cold') {
    if (id === 'lf-cold') { const cold = await setup(t); assert.equal((await cold.invoke([], { '--lf': true })).sent, 3); return; }
    if (id === 'lf') {
      const path = join(ctx.repo, 'tests/place-order.json'), doc = read(path); doc.initial_world.changed = true; write(path, doc);
      ctx.mode('failed'); await ctx.invoke(['place-order']); ctx.mode('passed');
      await ctx.invoke(['independent']);
      const scoped = await ctx.invoke(['independent'], { '--lf': true }); assert.equal(scoped.sent, 0); assert.equal(scoped.json.rows.length, 1); assert.equal(scoped.json.rows[0].cached, true);
      const result = await ctx.invoke([], { '--lf': true }); assert.equal(result.sent, 1); assert.equal(result.json.rows.length, 1);
    }
    const empty = await ctx.invoke([], { '--lf': true }); assert.equal(empty.sent, 0); assert.equal(empty.json.rows.length, 3); assert.equal(empty.code, 0); return;
  }
  if (id === 'clear') { const result = await ctx.invoke(['independent'], { '--cache-clear': true, '--lf': true }); assert.equal(result.sent, 1); assert.equal(result.json.rows.length, 1); return; }
  const dir = join(ctx.repo, '.pdd/cache/test');
  assert.ok(existsSync(dir), 'cache lives under .pdd/cache/test');
  if (id === 'ignored') {
    const result = git(ctx.repo, 'check-ignore', '.pdd/cache/test/probe'); assert.equal(result.status, 0, result.stderr);
    const linked = join(ctx.sandbox, 'linked'); const made = git(ctx.repo, 'worktree', 'add', '-b', 'cache-linked', linked); assert.equal(made.status, 0, made.stderr);
    assert.equal((await ctx.invoke([], {}, linked)).code, 0);
    assert.equal(git(linked, 'check-ignore', '.pdd/cache/test/probe').status, 0); return;
  }
  if (id === 'directory') { const result = await ctx.invoke(['.'], {}, join(ctx.repo, 'tests')); assert.equal(result.code, 0, result.err); assert.equal(result.json.rows.length, 3); assert.equal(result.sent, 0); return; }
  const names = readdirSync(dir, { recursive: true }).filter(name => name.endsWith('.json'));
  assert.ok(names.length > 0, 'cache contains bounded versioned metadata');
  const path = join(dir, 'stories.json');
  if (id === 'symlink') {
    const outside = join(ctx.sandbox, 'outside.json'); writeFileSync(outside, 'outside sentinel\n');
    const { unlinkSync } = await import('node:fs'); unlinkSync(path); symlinkSync(outside, path);
    const result = await ctx.invoke(); assert.equal(result.sent, 3); assert.equal(readFileSync(outside, 'utf8'), 'outside sentinel\n');
    assert.equal(result.json.warnings.filter(w => /cache/i.test(typeof w === 'string' ? w : JSON.stringify(w))).length, 1); return;
  }
  writeFileSync(path, id === 'malformed' ? '{broken' : '{"schema_version":"unknown","stories":[]}');
  const result = await ctx.invoke(); assert.equal(result.sent, 3);
  assert.equal(result.json.warnings.filter(w => /cache/i.test(typeof w === 'string' ? w : JSON.stringify(w))).length, 1, 'one damaged-cache warning');
});

async function pending(ctx) {
  ctx.mode('running');
  const sleep = ctx.ports.sleep;
  ctx.ports.sleep = async ms => { ctx.clock.now += ms; ctx.clock.interrupt(); };
  const result = await ctx.invoke(['place-order']);
  ctx.ports.sleep = sleep;
  assert.equal(result.code, 3, result.err);
  assert.equal(result.sent, 1);
  assert.ok(result.json.batch, 'pending checks have a recoverable batch');
  return result.json.batch;
}

test('TEST-CACHE saved read completion creates the first reusable pass', async t => {
  const ctx = await setup(t), batch = await pending(ctx);
  const path = join(ctx.repo, '.pdd/cache/test/stories.json');
  assert.ok(existsSync(path), 'exit 3 records an attempt without a pass');
  assert.equal(read(path).stories['user_stories/place-order.md'].pass, undefined);
  ctx.mode('passed');
  const recovered = await ctx.invoke([batch], { '--read': true });
  assert.equal(recovered.code, 0, recovered.err); assert.equal(recovered.sent, 0);
  const repeat = await ctx.invoke(['place-order']);
  assert.equal(repeat.code, 0, repeat.err);
  assert.equal(repeat.sent, 0, 'completed saved read supplies the pass cache');
  assert.equal(repeat.network, 0); assert.equal(repeat.gh, 0);
  assert.ok(repeat.json.rows.every(row => row.cached && row.calls === 0));
});

for (const newer of ['failed', 'passed']) test(`TEST-CACHE old interrupted read preserves newer ${newer} generation`, async t => {
  const ctx = await setup(t), batch = await pending(ctx);
  const path = join(ctx.repo, 'tests/place-order.json'), doc = read(path);
  doc.initial_world.changed = true; write(path, doc); ctx.mode(newer);
  const fresh = await ctx.invoke(['place-order']);
  assert.equal(fresh.code, newer === 'passed' ? 0 : 1, fresh.err);
  const cachePath = join(ctx.repo, '.pdd/cache/test/stories.json');
  assert.ok(existsSync(cachePath), 'newer attempt records its cache generation');
  const before = read(cachePath).stories['user_stories/place-order.md'];
  ctx.mode('passed');
  const recovered = await ctx.invoke([batch], { '--read': true });
  assert.equal(recovered.code, 0, recovered.err); assert.equal(recovered.sent, 0);
  assert.deepEqual(read(cachePath).stories['user_stories/place-order.md'], before,
    'old completion cannot replace newer changed-source pass or failure');
  const repeat = await ctx.invoke(['place-order'], newer === 'failed' ? { '--lf': true } : {});
  assert.equal(repeat.sent, newer === 'failed' ? 1 : 0); assert.equal(repeat.code, 0, repeat.err);
});

test('TEST-CACHE saved UUID read completion supplies reusable pass', async t => {
  const ctx = await setup(t);
  await pending(ctx);
  const id = checks(ctx.fake).at(-1).request.requestId;
  const files = readdirSync(ctx.state, { recursive: true }).filter(path => /(?:batch|summary)\.json$/.test(path));
  const before = files.map(path => [path, readFileSync(join(ctx.state, path), 'utf8')]);
  ctx.mode('passed');
  const recovered = await ctx.invoke([id], { '--read': true });
  assert.equal(recovered.code, 0, recovered.err); assert.equal(recovered.sent, 0);
  for (const [path, bytes] of before) assert.equal(readFileSync(join(ctx.state, path), 'utf8'), bytes, 'UUID read preserves saved batch projections');
  const repeat = await ctx.invoke(['place-order']);
  assert.equal(repeat.sent, 0, 'UUID completion populates the Story pass cache');
  assert.equal(repeat.network, 0); assert.equal(repeat.gh, 0);
  assert.ok(repeat.json.rows.every(row => row.cached && row.calls === 0));
});

// Oracles: LEAD 20:05 R1/R3 and DESIGN §6; fake interpreter only.
test('TEST-CACHE lf disjoint scope falls back to its normal uncached selection', async t => {
  const ctx = await setup(t);
  ctx.mode('failed'); await ctx.invoke(['place-order']); ctx.mode('passed');
  const result = await ctx.invoke(['independent'], { '--lf': true });
  assert.equal(result.sent, 1, 'failure elsewhere cannot suppress selected checks');
  assert.equal(result.json.rows.length, 1); assert.equal(result.json.rows[0].test, 'tests/independent.json');
  const retained = await ctx.invoke(['place-order'], { '--lf': true });
  assert.equal(retained.sent, 1, 'disjoint fallback preserves the other failure');
});

test('TEST-CACHE lf forgets deleted failed Stories and runs normal remaining selection', async t => {
  const ctx = await setup(t);
  ctx.mode('failed'); await ctx.invoke(['independent']); ctx.mode('passed');
  unlinkSync(join(ctx.repo, 'tests/independent.json')); unlinkSync(join(ctx.repo, 'user_stories/independent.md'));
  const result = await ctx.invoke([], { '--lf': true });
  assert.equal(result.sent, 2, 'deleted failure cannot make a cold remaining scope empty');
  assert.equal(result.json.rows.length, 2);
  for (const name of ['stories', 'lastfailed']) {
    const path = join(ctx.repo, `.pdd/cache/test/${name}.json`);
    assert.ok(existsSync(path), `${name} metadata persists completed selection`);
    const metadata = read(path);
    assert.ok(!JSON.stringify(metadata).includes('user_stories/independent.md'), `${name} forgets deleted Story`);
  }
});

for (const damage of ['missing', 'malformed', 'inconsistent']) test(`TEST-CACHE lastfailed ${damage} fails open once and heals`, async t => {
  const ctx = await setup(t); await prime(ctx, false);
  const path = join(ctx.repo, '.pdd/cache/test/lastfailed.json');
  assert.ok(existsSync(path), 'completed cache includes last-failed selection evidence');
  if (damage === 'missing') unlinkSync(path);
  else if (damage === 'malformed') writeFileSync(path, '{broken');
  else { const doc = read(path); doc.generation += 1; write(path, doc); }
  const result = await ctx.invoke(['independent'], { '--lf': true });
  assert.equal(result.sent, 1, 'untrusted last-failed metadata cannot suppress selected checks');
  assert.equal(result.json.warnings.filter(w => /cache/i.test(String(w))).length, 1);
  assert.ok(result.json.rows.every(row => !row.cached));
  const healed = await ctx.invoke(['independent'], { '--lf': true });
  assert.equal(healed.sent, 0); assert.equal(healed.json.rows.length, 1);
  assert.equal(healed.json.warnings.filter(w => /cache/i.test(String(w))).length, 0);
});

test('TEST-CACHE lf actually reads lastfailed through the injected filesystem', async t => {
  const ctx = await setup(t); await prime(ctx, false);
  const reads = [];
  ctx.ports.cacheFiles = { nonce: randomUUID, lstat: disk.lstatSync, mkdir: disk.mkdirSync, write: disk.writeFileSync,
    list: disk.readdirSync, rename: disk.renameSync, unlink: disk.unlinkSync, rmdir: disk.rmdirSync,
    exclude(root) { return join(root, '.git/info/exclude'); },
    read(path, ...args) { reads.push(String(path)); return disk.readFileSync(path, ...args); } };
  await ctx.invoke(['independent'], { '--lf': true });
  assert.ok(reads.some(path => path.endsWith('/lastfailed.json')), 'lf must consume designated selection metadata');
});

for (const json of [true, false]) test(`TEST-CACHE clear notice preserves ${json ? 'JSON' : 'text'} and selected scope`, async t => {
  const ctx = await setup(t); await prime(ctx, false);
  const result = await ctx.invoke(['independent'], { '--cache-clear': true, '--lf': true, '--json': json });
  assert.equal(result.sent, 1); assert.equal(result.code, 0);
  const notices = result.err.split('\n').filter(line => /test cache cleared/.test(line));
  assert.equal(notices.length, 1, 'exactly one clear progress notice');
  assert.match(notices[0], /Running 1 selected Stor/);
  assert.match(notices[0], /interpreter may reuse saved answers.*#535/);
  assert.doesNotMatch(ctx.ports.stdout.text, /test cache cleared/);
  if (json) { assert.equal(result.json.rows.length, 1); assert.ok(!result.json.warnings.some(w => /test cache cleared/.test(String(w)))); }
  else assert.match(ctx.ports.stdout.text, /independent/);
});

test('TEST-CACHE help describes current cache path and retained scope', () => {
  const help = renderHelp(['test']);
  assert.ok(help.includes('.pdd/cache/test/'));
  assert.ok(!help.includes('.pdd/test-cache/'));
  assert.match(help, /--cache-clear[^\n]*selected Stories/);
  assert.doesNotMatch(help, /--cache-clear[^\n]*runs all Stories/);
});
