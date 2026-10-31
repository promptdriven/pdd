import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import { chmodSync, existsSync, mkdirSync, readFileSync, readdirSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
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
async function prime(ctx) {
  const first = await ctx.invoke(); assert.equal(first.code, 0, first.err); assert.equal(first.sent, 3);
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
  const repeated = await prime(ctx);
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
    if (id === 'prompt') { const scoped = await ctx.invoke(['independent']); assert.equal(scoped.sent, 0); assert.equal(scoped.json.rows.length, 1); }
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
      const scoped = await ctx.invoke(['independent'], { '--lf': true }); assert.equal(scoped.sent, 0); assert.equal(scoped.json.rows.length, 0);
      const result = await ctx.invoke([], { '--lf': true }); assert.equal(result.sent, 1); assert.equal(result.json.rows.length, 1);
    }
    const empty = await ctx.invoke([], { '--lf': true }); assert.equal(empty.sent, 0); assert.equal(empty.json.rows.length, 0); assert.equal(empty.code, 0); return;
  }
  if (id === 'clear') { const result = await ctx.invoke(['independent'], { '--cache-clear': true, '--lf': true }); assert.equal(result.sent, 3); assert.equal(result.json.rows.length, 3); return; }
  const dir = join(ctx.repo, '.pdd/test-cache');
  assert.ok(existsSync(dir), 'cache lives under .pdd/test-cache');
  if (id === 'ignored') {
    const result = git(ctx.repo, 'check-ignore', '.pdd/test-cache/probe'); assert.equal(result.status, 0, result.stderr);
    const linked = join(ctx.sandbox, 'linked'); const made = git(ctx.repo, 'worktree', 'add', '-b', 'cache-linked', linked); assert.equal(made.status, 0, made.stderr);
    assert.equal((await ctx.invoke([], {}, linked)).code, 0);
    assert.equal(git(linked, 'check-ignore', '.pdd/test-cache/probe').status, 0); return;
  }
  if (id === 'directory') { const result = await ctx.invoke(['.'], {}, join(ctx.repo, 'tests')); assert.equal(result.code, 0, result.err); assert.equal(result.json.rows.length, 3); assert.equal(result.sent, 0); return; }
  const names = readdirSync(dir, { recursive: true }).filter(name => name.endsWith('.json'));
  assert.ok(names.length > 0, 'cache contains bounded versioned metadata');
  const path = join(dir, names[0]);
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
