import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { cpSync, mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { spawnSync } from 'node:child_process';
import { compareAutopilot, comparisonTable, main, validateReplay } from '../scripts/autopilot-compare.mjs';

const root = resolve('.');
const fixture = () => JSON.parse(readFileSync(new URL('./fixtures/autopilot-compare-backlog.json', import.meta.url)));
const capture = () => ({ text: '', write(text) { this.text += text; } });
let shared;
const self = () => shared ??= compareAutopilot({ oldRoot: root, newRoot: root, replay: fixture() });

test('real ticks replay the same observations with stable decisions and counted reads/writes', async () => {
  const replay = fixture(), report = await self();
  assert.equal(report.inputSha256, createHash('sha256').update(JSON.stringify(replay)).digest('hex'));
  assert.equal(report.selfComparison, true);
  assert.equal(report.comparison.length, 7);
  assert.ok(report.comparison.every(f => f.decisionsEqual && f.callsEqual && f.writesEqual));
  assert.deepEqual(report.old.totals, report.new.totals);
  assert.ok(report.new.totals.restCalls > 0);
  assert.ok(report.new.totals.restWrites > 0);
  assert.ok(report.new.totals.graphqlCalls > 0);
  assert.equal(report.new.totals.graphqlWrites, 0, 'GraphQL POST queries must remain reads');
  assert.equal(report.new.totals.writes, report.new.totals.restWrites);
  assert.ok(report.new.frames.flatMap(f => f.writes).every(w => /^[a-f0-9]{64}$/.test(w.payloadSha256)));
  assert.equal(report.new.totals.deliveries, report.new.frames.reduce((n, f) => n + f.decisions.delivered.length, 0));
  const initial = report.new.frames[0];
  assert.deepEqual(initial.decisions.delivered.find(d => d.kind === 'dependency-review').issues, [1, 2, 3, 4, 5, 6, 7]);
  assert.equal(initial.decisions.pendingReview, false);
  for (const f of report.new.frames) for (const d of f.decisions.delivered) {
    assert.ok(d.issues.every(i => (typeof i === 'number' ? i : i.number) !== 8), 'untrusted issue cannot enter trusted work');
  }
  const claimed = report.new.frames.find(f => f.name === 'other-machine-claim');
  const offer = claimed.decisions.delivered.flatMap(d => d.kind === 'work' ? d.issues : []).find(i => i.number === 5);
  assert.deepEqual(offer, { number: 5, eligible: false, claimed: true, expiredClaim: false });
  assert.ok(!claimed.decisions.eligible.includes(5));
  const closed = report.new.frames.find(f => f.name === 'issue-closed');
  assert.ok(!closed.decisions.eligible.includes(6));
  assert.ok(closed.decisions.delivered.every(d => d.kind !== 'work' || d.issues.every(i => i.number !== 6)));
  const edited = report.new.frames.find(f => f.name === 'trusted-edit');
  assert.deepEqual(edited.decisions.delivered.find(d => d.kind === 'dependency-review').issues, [1]);
});

test('selected new tick adds a fake write and comparison detects the change', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-compare-selected-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const src = join(dir, 'src'); mkdirSync(src);
  writeFileSync(join(dir, 'package.json'), JSON.stringify({ type: 'module', version: 'instrumented-tick' }));
  for (const name of ['issue-dependencies-intake', 'github-calls', 'autopilot-store']) {
    writeFileSync(join(src, `${name}.mjs`), `export * from ${JSON.stringify(pathToFileURL(resolve('src', `${name}.mjs`)).href)};\n`);
  }
  const native = JSON.stringify(pathToFileURL(resolve('src/autopilot-launcher.mjs')).href);
  writeFileSync(join(src, 'autopilot-launcher.mjs'), `
    export * from ${native};
    import { tickAutopilot as tick } from ${native};
    export async function tickAutopilot(file, ports) {
      const result = await tick(file, ports);
      await ports.run('gh', ['api', '--include', '--method', 'PATCH', 'repos/acme/widgets/issues/2', '--input', '-'],
        {input: JSON.stringify({labels:['extra']})});
      return result;
    }
  `);
  const report = await compareAutopilot({ oldRoot: root, newRoot: dir, replay: fixture() });
  assert.equal(report.selfComparison, false);
  assert.equal(report.new.version, 'instrumented-tick');
  assert.equal(report.new.totals.writes - report.old.totals.writes, 6);
  assert.ok(report.comparison.slice(1).every(f => !f.writesEqual && f.writeDelta === 1));
  assert.ok(report.new.frames.slice(1).every(f => f.writes.some(c => c.endpoint === 'repos/acme/widgets/issues/2' && c.method === 'PATCH')));

  // Keep routes, request counts and status unchanged. Only the label payload differs.
  const other = mkdtempSync(join(tmpdir(), 'pdd-compare-payload-'));
  t.after(() => rmSync(other, { recursive: true, force: true }));
  cpSync(dir, other, { recursive: true });
  const launcher = join(other, 'src/autopilot-launcher.mjs');
  writeFileSync(launcher, readFileSync(launcher, 'utf8').replace("labels:['extra']", "labels:['changed-payload']"));
  const payloadOnly = await compareAutopilot({ oldRoot: other, newRoot: dir, replay: fixture() });
  assert.deepEqual(payloadOnly.old.totals, payloadOnly.new.totals);
  assert.ok(payloadOnly.comparison.every(f => f.callsEqual));
  assert.ok(payloadOnly.comparison.slice(1).every(f => !f.writesEqual && f.writeDelta === 0), 'same-route payload changes must be visible');
});

test('external replay leaves AI requests pending without fabricating answers', async () => {
  const replay = fixture(); replay.synthetic = false; delete replay.completeIndependent;
  replay.frames = replay.frames.slice(0, 2);
  const report = await compareAutopilot({ oldRoot: root, newRoot: root, replay });
  assert.equal(report.synthetic, false);
  assert.equal(report.new.frames[0].decisions.pendingReview, true);
  assert.equal(report.new.totals.graphqlWrites, 0);
  assert.equal(report.new.frames.flatMap(f => f.writes).filter(c => /\/issues\/\d+\/comments$/.test(c.endpoint)).length, 1,
    'only the untrusted-author acknowledgment is written; no dependency review answers');
});

test('selected source command ports stay isolated through ticks, completion and idle callbacks', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-compare-environment-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const keys = ['CODEX_HOME', 'CLAUDE_CONFIG_DIR', 'GH_CONFIG_DIR', 'GH_HOST', 'GH_TOKEN', 'GITHUB_TOKEN'];
  const saved = Object.fromEntries(keys.map(key => [key, process.env[key]]));
  t.after(() => {
    for (const key of keys) {
      if (saved[key] === undefined) delete process.env[key];
      else process.env[key] = saved[key];
    }
  });
  for (const key of keys) process.env[key] = join(dir, `harmless-${key}`);
  const src = join(dir, 'src'); mkdirSync(src);
  writeFileSync(join(dir, 'package.json'), JSON.stringify({ type: 'module', version: 'environment-probe' }));
  for (const name of ['issue-dependencies-intake', 'github-calls', 'autopilot-store']) {
    writeFileSync(join(src, `${name}.mjs`), `export * from ${JSON.stringify(pathToFileURL(resolve('src', `${name}.mjs`)).href)};\n`);
  }
  const native = JSON.stringify(pathToFileURL(resolve('src/autopilot-launcher.mjs')).href);
  const launcher = join(src, 'autopilot-launcher.mjs');
  writeFileSync(launcher, `
    export * from ${native};
    import * as native from ${native};
    export const observations = [];
    let idle = false;
    function observe(ports, phase) {
      return {...ports,
        run: async (command, args, options) => {
          observations.push({phase: idle ? 'idle' : phase, command,
            inherited: ${JSON.stringify(keys)}.filter(key => options?.env?.[key] === process.env[key]),
            home: options?.env?.HOME, path: options?.env?.PATH});
          return ports.run(command, args, options);
        },
        armCoordinatorIdle: (identity, options) => ports.armCoordinatorIdle(identity, {...options,
          resume: async () => { idle = true; try { return await options.resume(); } finally { idle = false; } }
        })
      };
    }
    export const runAutopilotLauncher = (input, ports) => native.runAutopilotLauncher(input, observe(ports, 'start'));
    export const tickAutopilot = (file, ports) => native.tickAutopilot(file, observe(ports, 'tick'));
    export const requestAutopilotCompletion = (input, ports) => native.requestAutopilotCompletion(input, observe(ports, 'completion'));
  `);
  const report = await compareAutopilot({ oldRoot: root, newRoot: dir, replay: fixture() });
  const { observations } = await import(pathToFileURL(launcher).href);
  for (const phase of ['start', 'tick', 'completion', 'idle']) {
    const commands = observations.filter(o => o.phase === phase);
    assert.ok(commands.length > 0, phase);
    assert.deepEqual(commands.filter(o => o.inherited.length > 0).map(o => ({ command: o.command, inherited: o.inherited })), [], phase);
    assert.ok(commands.every(o => o.home && o.home !== process.env.HOME && o.path), phase);
  }
  assert.ok(report.comparison.every(f => f.decisionsEqual && f.callsEqual && f.writesEqual));
});

test('malformed recordings fail before either source is loaded', async () => {
  const variants = [
    r => { r.frames[1].at = r.frames[0].at; },
    r => { r.frames[0].snapshot.repository = 'other/repo'; },
    r => { r.frames[0].snapshot.list.rows['1'].number = 2; },
    r => { r.synthetic = false; },
    r => { delete r.frames[0].snapshot.issues['1'].kinds.comments; },
    r => { r.frames[0].snapshot.issues['1'].kinds.blockedBy = [{ html_url: 'https://github.com/acme/widgets/issues/999' }]; },
    r => { r.frames[0].snapshot.list.rows['1'].comments = 1; },
    r => { r.completeIndependent = false; r.frames[0].snapshot.list.rows['1'].issue_dependencies_summary.blocked_by = 1; },
    r => { const pages = r.frames[0].snapshot.issues['1'].kinds; pages.timeline = [{ id: 1, event: 'labeled', actor: { login: 'acme' }, created_at: '2026-11-07T12:00:00Z' }]; pages.timeline.push({ ...pages.timeline[0] }); },
  ];
  for (const change of variants) {
    const replay = fixture(); change(replay);
    await assert.rejects(compareAutopilot({ oldRoot: '/missing/old', newRoot: '/missing/new', replay }), error => {
      assert.equal(error.code, undefined); // Input validation, not ENOENT before the replay boundary.
      return true;
    });
  }
  assert.equal(validateReplay(fixture()).frames.length, 7);
});

test('CLI prints a machine-readable comparison through the real process', () => {
  const result = spawnSync(process.execPath, ['scripts/autopilot-compare.mjs', '--old', root, '--new', root, '--json'],
    { encoding: 'utf8', timeout: 60000, maxBuffer: 8 * 1024 * 1024 });
  assert.equal(result.status, 0, result.stderr);
  const report = JSON.parse(result.stdout);
  assert.equal(report.schema_version, 'pdd.autopilot-compare.v1');
  assert.equal(report.old.frames.length, 7);
  assert.equal(report.comparison.length, 7);
  assert.ok(result.stdout.endsWith('\n'));
  const table = comparisonTable(report);
  for (const metric of ['restCalls', 'restWrites', 'graphqlCalls', 'graphqlWrites', 'deliveries']) assert.ok(table.includes(`| ${metric} |`));
  assert.ok(table.includes(report.inputSha256));
});

test('CLI refuses invalid options and source failures without printing a result table', async () => {
  for (const argv of [[], ['--old'], ['--old', '.', '--new', '.', '--old', '.'], ['--other'], ['--json']]) {
    const stdout = capture(), stderr = capture();
    assert.equal(await main(argv, { stdout, stderr }), 2);
    assert.equal(stdout.text, ''); assert.ok(stderr.text.length > 0);
  }
  const stdout = capture(), stderr = capture();
  assert.equal(await main(['--old', '/missing/old', '--new', '.'], { stdout, stderr }), 1);
  assert.equal(stdout.text, ''); assert.ok(stderr.text.endsWith('\n'));
});
