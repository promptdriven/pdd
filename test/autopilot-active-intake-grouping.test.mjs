import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync, readFileSync, mkdirSync, existsSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { coreWorld } from './helpers/core-world.mjs';
import {
  INTAKE_MODES,
  intakeMode,
  issueVersion,
  readCard,
  readImprovement,
  improveCommand,
  cardEnvironment,
  rankReadyRows,
  wouldPick,
  readIntake,
  intakeFolders,
} from '../src/autopilot-intake.mjs';
import {
  normalizeAreaPath,
  normalizeAreaList,
  parseGitHubIssueUrl,
  issueAreas,
  areasOverlap,
  isSmallCard,
  groupReadyIssues,
} from '../src/autopilot-areas.mjs';
import { coreSettings } from '../src/autopilot-core.mjs';
import { runAutopilotLauncher } from '../src/autopilot-launcher.mjs';

const intakeJobs = w => w.started.filter(job => job.role === 'intake');
const improveJobs = w => w.started.filter(job => job.role === 'intake-improve');
const workJobs = w => w.started.filter(job => job.role !== 'intake' && job.role !== 'intake-improve');

function finishAnswerJob(w, role, issue, payload, { code = 0 } = {}) {
  const job = [...w.started].reverse().find(j => j.role === role && j.issue === issue);
  assert.ok(job, `expected ${role} job for #${issue}`);
  w.alive.delete(job.pid);
  if (payload !== undefined) {
    const outFile = job.args[job.args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, typeof payload === 'string' ? payload : JSON.stringify(payload));
  }
  writeFileSync(job.exit, JSON.stringify({ code, signal: null, at: w.now() }));
  return job;
}

const finishCard = (w, issue, payload, opts) => finishAnswerJob(w, 'intake', issue, payload, opts);
const finishImprove = (w, issue, payload, opts) => finishAnswerJob(w, 'intake-improve', issue, payload, opts);

async function seedCardFile(w, issueOrNum, cardObj, extra = {}) {
  const num = typeof issueOrNum === 'number' ? issueOrNum : issueOrNum.number;
  const rows = await w.ports().listIssues();
  const row = rows.find(r => r.number === num);
  assert.ok(row, `expected open issue #${num}`);
  const f = intakeFolders(w.root);
  mkdirSync(f.cards, { recursive: true, mode: 0o700 });
  const parsed = readCard(cardObj, { selfIssue: row.number });
  assert.ok(parsed, `card fixture for #${row.number} must be valid`);
  writeFileSync(join(f.cards, `${row.number}.json`), JSON.stringify({
    issue: row.number,
    version: issueVersion(row),
    at: w.now(),
    agent: { kind: 'codex', model: null },
    seconds: 1,
    native: null,
    card: parsed,
    ...extra,
  }, null, 1) + '\n');
}

test('active-intake 1: intakeMode("active"), coreSettings, CLI/launcher without opt-in label, and gating unvetted issues', async t => {
  assert.deepEqual(INTAKE_MODES, ['off', 'shadow', 'active']);
  assert.equal(intakeMode('active'), 'active');
  assert.equal(intakeMode('shadow'), 'shadow');
  assert.equal(intakeMode('off'), 'off');
  assert.equal(intakeMode('unknown'), 'off');

  assert.equal('intake' in coreSettings({ autopilot: { mode: 'auto', engine: 'core' } }), false, 'omitted when unset for backward compatibility');
  assert.equal(coreSettings({ autopilot: { mode: 'auto', engine: 'core', intake: 'active' } }).intake, 'active');
  assert.equal(coreSettings({ autopilot: { mode: 'auto', engine: 'core', intake: 'bogus' } }).intake, 'off');

  const w = await coreWorld(t, { settings: { runs: 2 } });
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel');
  const pkgRoot = join(w.dir, 'pkg');
  mkdirSync(pkgRoot, { recursive: true });
  writeFileSync(join(pkgRoot, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.27' }));
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], testCommand: 'npm test', runs: 2 } }));

  const stateRoot = join(w.dir, 'launcher-state');
  mkdirSync(stateRoot, { recursive: true });
  const env = { HOME: process.env.HOME, PATH: process.env.PATH };
  const launcherPorts = {
    stateRoot,
    now: w.now,
    env,
    timer: async () => true,
    warn: () => {},
    doctorPorts: {
      run: async (command, args, options = {}) => {
        if (command === 'git') {
          const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' });
          return { code: r.status, stdout: r.stdout, stderr: r.stderr };
        }
        return { code: 0, stdout: '', stderr: '' };
      },
      onSelection: undefined,
    },
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }),
    pathDiagnostic: () => [],
    run: async (command, args, options = {}) => {
      if (command === 'gh') {
        if (args[0] === 'auth' && args[1] === 'status') return { code: 0, stdout: 'Logged in', stderr: '' };
        if (args[0] === 'repo' && args[1] === 'view') {
          return { code: 0, stdout: JSON.stringify({ nameWithOwner: 'acme/widgets', defaultBranchRef: { name: 'main' } }), stderr: '' };
        }
        return w.gh(args, options);
      }
      if (command === 'git') {
        const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' });
        return { code: r.status, stdout: r.stdout, stderr: r.stderr };
      }
      return { code: 0, stdout: '', stderr: '' };
    },
    machineGuard: w.machineGuard,
    corePorts: {
      jobs: w.jobs,
      checkBase: async () => ({ exitCode: 0, message: 'ok' }),
      agentReady: async () => true,
      reportRoot: w.reportRoot,
    },
  };

  // Without --label and without active intake, launcher refuses with NO_LABEL.
  const refused = await runAutopilotLauncher({ command: 'start', cwd, packageRoot: pkgRoot, env, issues: [] }, launcherPorts);
  assert.equal(refused.exitCode, 1);
  assert.match(refused.message, /opt-in label/);

  // Create open issues WITHOUT any pdd:autopilot label.
  w.issue(10, { title: 'Fix trim bug in src/trim.mjs', body: 'src/trim.mjs fails on tabs.' });
  w.issue(11, { title: 'Choose pricing tier model', body: 'Should free tier allow 5 or 10 seats?' });

  // Starting with --intake active succeeds without --label, runs first tick, and does NOT blindly claim unvetted issues!
  const started = await runAutopilotLauncher({
    command: 'start',
    cwd,
    packageRoot: pkgRoot,
    env,
    issues: [],
    intake: 'active',
    doctorPorts: undefined,
  }, {
    ...launcherPorts,
    doctorPorts: {
      ...launcherPorts.doctorPorts,
      resolveAgent: async () => ({ agent: { id: 'codex', kind: 'codex', command: 'codex', env: {} } }),
    },
  });
  // Even if doctor checks real binaries in test-home, verify state file / direct active core selection deterministically:
  if (started.exitCode === 0) {
    assert.match(started.message, /ready issues from active intake/);
  }
  assert.equal(workJobs(w).length, 0, 'unvetted issues are never blindly claimed in active mode');

  // Verify status & intake commands with saved active state and no label.
  const stateId = createHash('sha256').update(cwd).digest('hex').slice(0, 20);
  const stateFile = join(stateRoot, `${stateId}.json`);
  writeFileSync(stateFile, JSON.stringify({
    enabled: true,
    cwd,
    repo: 'acme/widgets',
    defaultBranch: 'main',
    baseBranch: 'main',
    coordinatorId: 'coord-a',
    machine: 'machine-a',
    engine: 'core',
    intake: 'active',
    agent: { id: 'codex', kind: 'codex', command: 'codex' },
    packageRoot: pkgRoot,
  }));
  const statusOut = await runAutopilotLauncher({ command: 'status', cwd, packageRoot: pkgRoot, env, issues: [] }, launcherPorts);
  assert.equal(statusOut.exitCode, 0);
  assert.match(statusOut.message, /active intake \(ready cards\)/);
  assert.doesNotMatch(statusOut.message, /No opt-in label:/);

  const intakeOut = await runAutopilotLauncher({ command: 'intake', cwd, packageRoot: pkgRoot, env, issues: [] }, launcherPorts);
  assert.equal(intakeOut.exitCode, 0);
  assert.match(intakeOut.message, /^Intake: active on this machine\./);
  assert.match(intakeOut.message, /active; ready cards drive selection/);

  // Now run core ticks directly with labelRequired: true, label: null, intake: 'active'.
  const w2 = await coreWorld(t, { settings: { runs: 2 } });
  w2.settings.intake = 'active';
  w2.settings.labelRequired = true;
  w2.settings.label = null;
  w2.issue(10, { title: 'Fix trim bug in src/trim.mjs', body: 'Clear reproduction.' });
  w2.issue(11, { title: 'Decide billing currency', body: 'Product question.' });
  w2.issue(12, { title: 'Duplicate of #10', body: 'Same trim bug.' });

  const t1 = await w2.tick();
  assert.equal(workJobs(w2).length, 0, 'tick 1 starts 0 build jobs before cards exist');
  assert.doesNotMatch(t1.message, /no opt-in label/, 'active mode does not hold on missing opt-in label');
  assert.deepEqual(intakeJobs(w2).map(j => j.issue), [10, 11], 'starts bounded intake card jobs');

  finishCard(w2, 10, {
    class: 'ready',
    reason: 'Clear bug in src/trim.mjs.',
    confidence: 0.92,
    areas: ['src/trim.mjs'],
    group_with: [],
    size: 'medium',
    model: 'gpt-test',
  });
  finishCard(w2, 11, {
    class: 'person',
    reason: 'Needs currency choice.',
    confidence: 0.9,
    question: 'USD or EUR?',
    areas: ['src/billing.mjs'],
    model: 'gpt-test',
  });

  // Tick 2: collectActiveIntake promotes finished card #10 before core selection -> #10 starts immediately, #11 stays gated, #12 gets card job!
  await w2.tick();
  assert.deepEqual(workJobs(w2).map(j => `${j.issue}:${j.role}`), ['10:build'], 'only vetted ready card #10 starts');
  assert.deepEqual(intakeJobs(w2).map(j => j.issue), [10, 11, 12]);

  // Verify stale version gating: #13 gets a ready card, then human edits #13 before slot opens -> stale card does not start!
  w2.issue(13, { title: 'Add flag --quiet', body: 'Initial spec.' });
  finishCard(w2, 12, { class: 'duplicate', canonical: 10, reason: 'Same as #10.', confidence: 0.95 });
  await w2.tick();
  finishCard(w2, 13, { class: 'ready', reason: 'Clear flag.', confidence: 0.9, areas: ['src/flags.mjs'], size: 'medium' });
  w2.github.comment(13, 'Wait — also change the exit code contract.', 'acme');
  await w2.tick();
  assert.equal(workJobs(w2).some(j => j.issue === 13), false, 'stale ready card after new human comment never starts blindly');
});

test('active-intake 2: areas, area_hint alias, group_with, size parsing, and area overlap rules', () => {
  assert.equal(normalizeAreaPath('  `./src//intake/cards.mjs/` '), 'src/intake/cards.mjs');
  assert.equal(normalizeAreaPath('/prompts/cli/autopilot-intake.prompt.md'), 'prompts/cli/autopilot-intake.prompt.md');
  assert.equal(normalizeAreaPath('area: Parser'), 'area:parser');
  assert.equal(normalizeAreaPath('../secrets.txt'), null);
  assert.equal(normalizeAreaPath('https://example.com/a/b'), null);
  assert.equal(normalizeAreaPath('two words/path.mjs'), null);

  const card = readCard({
    class: 'ready',
    reason: 'Small parser fix.',
    confidence: 0.88,
    areas: ['./src/parser.mjs', '../bad', 'src/parser.mjs', 'prompts/cli/parser.prompt.md'],
    area_hint: ['test/parser.test.mjs', 'src/a.mjs', 'src/b.mjs', 'src/c.mjs', 'src/d.mjs'],
    group_with: [15, 12, 15, -3, 0, 'bad', 10],
    size: 'small',
    model: 'gpt-test',
  }, { selfIssue: 10 });

  assert.deepEqual(card.areas, [
    'src/parser.mjs',
    'prompts/cli/parser.prompt.md',
    'test/parser.test.mjs',
    'src/a.mjs',
    'src/b.mjs',
    'src/c.mjs',
  ], 'normalized, deduplicated, and capped at 6');
  assert.deepEqual(card.area_hint, card.areas, 'area_hint stays aliased for shadow compatibility');
  assert.deepEqual(card.group_with, [12, 15], 'sorted unique positive integers excluding selfIssue');
  assert.equal(card.size, 'small');
  assert.equal(isSmallCard(card), true);

  // Disjoint top-level files in src/ must NOT collide, while nested module folders, prompt stems, and area:* labels DO collide.
  assert.equal(areasOverlap(['src/alpha.mjs'], ['src/beta.mjs']).overlap, false);
  assert.equal(areasOverlap(['src/billing/invoice.mjs'], ['src/billing/tax.mjs']).overlap, true);
  assert.equal(areasOverlap(['src/billing'], ['src/billing/tax.mjs']).overlap, true);
  assert.equal(areasOverlap(['prompts/cli/autopilot-intake.prompt.md'], ['src/autopilot-intake.mjs']).overlap, true);
  assert.equal(areasOverlap(['area:intake'], ['area:intake']).overlap, true);
  assert.equal(areasOverlap(['area:intake'], ['area:merge']).overlap, false);

  const rowAreas = issueAreas(
    { title: 'Fix bug in src/lexer/scan.mjs', body: 'Touches test/lexer.test.mjs', labels: [{ name: 'area:Lexer' }] },
    { areas: ['prompts/cli/lexer.prompt.md'] },
  );
  assert.deepEqual(rowAreas, ['prompts/cli/lexer.prompt.md', 'area:lexer', 'src/lexer/scan.mjs', 'test/lexer.test.mjs']);
});

test('active-intake 3a: claims 2-3 small ready grouped issues into one job/PR (Closes #A, Closes #B), closes all on merge, and releases companions on failure', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  w.settings.intake = 'active';
  w.settings.labelRequired = true;
  w.settings.label = null;

  // 4 small issues in the same module cluster -> first 3 (#21, #22, #23) group into 1 job; #24 serializes behind them!
  const r21 = w.issue(21, { title: 'Trim leading tabs in widget parser', body: 'In src/widget-parser.mjs.' });
  const r22 = w.issue(22, { title: 'Trim trailing CR in widget parser', body: 'In src/widget-parser.mjs.' });
  const r23 = w.issue(23, { title: 'Reject NUL byte in widget parser', body: 'In src/widget-parser.mjs.' });
  const r24 = w.issue(24, { title: 'Normalize newline in widget parser', body: 'In src/widget-parser.mjs.' });

  await seedCardFile(w, r21, { class: 'ready', reason: 'Small fix 1.', confidence: 0.95, areas: ['src/widget-parser.mjs'], group_with: [22, 23], size: 'small' });
  await seedCardFile(w, r22, { class: 'ready', reason: 'Small fix 2.', confidence: 0.93, areas: ['src/widget-parser.mjs'], group_with: [21], size: 'small' });
  await seedCardFile(w, r23, { class: 'ready', reason: 'Small fix 3.', confidence: 0.91, areas: ['src/widget-parser.mjs'], group_with: [21, 22], size: 'small' });
  await seedCardFile(w, r24, { class: 'ready', reason: 'Small fix 4.', confidence: 0.9, areas: ['src/widget-parser.mjs'], group_with: [21], size: 'small' });

  await w.tick();
  assert.deepEqual(workJobs(w).map(j => `${j.issue}:${j.role}`), ['21:build'], 'one grouped build job starts; #24 waits because src/widget-parser.mjs is busy');

  // All 3 grouped issues (#21, #22, #23) hold pdd:working on GitHub, while #24 does not.
  for (const n of [21, 22, 23]) assert.ok(w.labels(n).includes('pdd:working'), `#${n} claimed with pdd:working`);
  assert.equal(w.labels(24).includes('pdd:working'), false, '#24 not claimed while area is busy');

  // Primary job prompt includes companion specs and instructs closing all grouped issues.
  const buildJob = w.job(21, 'build');
  assert.match(buildJob.input, /Companion Issue #22: Trim trailing CR in widget parser/);
  assert.match(buildJob.input, /Companion Issue #23: Reject NUL byte in widget parser/);
  assert.match(buildJob.input, /Closes #21, Closes #22, Closes #23/);

  // Primary claim record advertises group and areas.
  assert.ok(w.comments(21).some(body => body.includes('"group":[21,22,23]') && body.includes('"src/widget-parser.mjs"')));

  // Build finishes WITHOUT writing Closes #22 / #23 itself -> writeEvidenceBlock adds Closes #21, Closes #22, Closes #23!
  const { pr } = w.build(21, { body: 'Ship grouped widget-parser fixes.\n\nRuntime: PASS' });
  await w.tick(); // starts review + suite
  w.review(21, 'PASS');
  w.suite(21, 0);
  await w.tick(); // writes evidence block and merges PR!

  assert.equal(pr.merged, true, 'grouped PR merged');
  assert.match(pr.body, /Closes #21/);
  assert.match(pr.body, /Closes #22/);
  assert.match(pr.body, /Closes #23/);
  for (const n of [21, 22, 23]) {
    assert.equal(w.github.issues.get(n).state, 'closed', `#${n} closed on merge`);
    assert.equal(w.labels(n).includes('pdd:working'), false, `#${n} pdd:working removed`);
  }

  // In the same/next tick after merge freed src/widget-parser.mjs, #24 is now free to start!
  await w.tick();
  assert.ok(workJobs(w).some(j => j.issue === 24 && j.role === 'build'), '#24 starts once grouped job releases the area');

  // Also verify companion cleanup when a grouped job fails/ends: no dangling pdd:working on companions!
  const r25 = w.issue(25, { title: 'Small config fix A', body: 'In src/cfg/load.mjs.' });
  const r26 = w.issue(26, { title: 'Small config fix B', body: 'In src/cfg/load.mjs.' });
  await seedCardFile(w, r25, { class: 'ready', reason: 'Small A.', confidence: 0.9, areas: ['src/cfg/load.mjs'], group_with: [26], size: 'small' });
  await seedCardFile(w, r26, { class: 'ready', reason: 'Small B.', confidence: 0.9, areas: ['src/cfg/load.mjs'], group_with: [25], size: 'small' });
  await w.tick();
  assert.ok(w.labels(25).includes('pdd:working') && w.labels(26).includes('pdd:working'));
  w.finish(25, 'build', { result: { outcome: 'failed', kind: 'job', component: 'agent', code: 'broken', cause: 'Could not compile' } });
  await w.tick();
  assert.equal(w.labels(25).includes('pdd:working'), false);
  assert.equal(w.labels(26).includes('pdd:working'), false, 'companion #26 pdd:working cleanly released when grouped job ends');
});

test('active-intake 3b: serializes overlapping areas across parallel slots while running disjoint areas in parallel', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  w.settings.intake = 'active';
  w.settings.labelRequired = true;
  w.settings.label = null;

  const r31 = w.issue(31, { title: 'Refactor invoice totals', body: 'Large update in src/billing/invoice.mjs.' });
  const r32 = w.issue(32, { title: 'Adjust invoice rounding', body: 'Large update in prompts/cli/invoice.prompt.md.' });
  await seedCardFile(w, r31, { class: 'ready', reason: 'Clear large refactor.', confidence: 0.9, areas: ['src/billing/invoice.mjs'], size: 'large' });
  await seedCardFile(w, r32, { class: 'ready', reason: 'Clear large prompt change.', confidence: 0.9, areas: ['prompts/cli/invoice.prompt.md'], size: 'large' });

  // Slot 1 takes #31; slot 2 stays free because #32 overlaps on stem `invoice`!
  await w.tick();
  assert.deepEqual(workJobs(w).map(j => `${j.issue}:${j.role}`), ['31:build']);

  // On the next tick with only #32 waiting and slot 2 still open, tick message reports area-busy hold reason!
  const heldTick = await w.tick();
  assert.match(heldTick.message, /intake held: area busy \(#31 touches /);
  assert.deepEqual(workJobs(w).map(j => `${j.issue}:${j.role}`), ['31:build']);

  // Now add disjoint #33 touching src/cli/help.mjs -> slot 2 starts #33 in parallel and tells #33 about #31's areas!
  const r33 = w.issue(33, { title: 'Improve CLI help spacing', body: 'Update src/cli/help.mjs.' });
  await seedCardFile(w, r33, { class: 'ready', reason: 'Disjoint CLI change.', confidence: 0.9, areas: ['src/cli/help.mjs'], size: 'medium' });
  await w.tick();
  assert.deepEqual(workJobs(w).map(j => `${j.issue}:${j.role}`), ['31:build', '33:build'], 'disjoint area runs in parallel slot 2 while #32 waits');
  assert.match(w.job(33, 'build').input, /#31 Refactor invoice totals: areas src\/billing\/invoice\.mjs/);
});

test('active-intake 4: ranks unblockers, active group continuations, high-clarity small/bug wins, and priority ahead of oldest age', async t => {
  const rows = [
    { number: 40, created_at: '2026-10-01T00:00:00Z', title: 'Old large cleanup', labels: [] },
    { number: 41, created_at: '2026-10-05T00:00:00Z', title: 'High priority medium task', labels: [{ name: 'p1' }] },
    { number: 42, created_at: '2026-10-10T00:00:00Z', title: 'Crisp small bug fix', labels: [{ name: 'bug' }] },
    { number: 43, created_at: '2026-10-12T00:00:00Z', title: 'Follow-up in active group 99', labels: [] },
    { number: 44, created_at: '2026-10-15T00:00:00Z', title: 'Unblocks two downstream issues', labels: [], issue_dependencies_summary: { blocked_by: 0, total_blocking: 2 } },
  ];
  const cardByIssue = {
    40: { class: 'ready', reason: 'Large cleanup.', confidence: 0.7, size: 'large', areas: ['src/old.mjs'], group_with: [] },
    41: { class: 'ready', reason: 'Medium p1 work.', confidence: 0.72, size: 'medium', areas: ['src/p1.mjs'], group_with: [] },
    42: { class: 'ready', reason: 'Small crisp bug.', confidence: 0.95, size: 'small', areas: ['src/bug.mjs'], group_with: [] },
    43: { class: 'ready', reason: 'Continues group #99.', confidence: 0.8, size: 'medium', areas: ['src/grp.mjs'], group_with: [99] },
    44: { class: 'ready', reason: 'Unblocker.', confidence: 0.75, size: 'medium', areas: ['src/unblock.mjs'], group_with: [] },
  };
  const cards = new Map(rows.map(row => [row.number, {
    issue: row.number,
    version: issueVersion(row),
    card: readCard(cardByIssue[row.number], { selfIssue: row.number }),
  }]));

  const ranked = rankReadyRows(rows, cards, { activeGroupIssues: new Set([99]) }).map(r => r.number);
  assert.deepEqual(ranked, [44, 43, 42, 41, 40]);
  assert.deepEqual(wouldPick(rows, cards, { activeGroupIssues: [99] }), [44, 43, 42, 41, 40]);

  // Verify core active intake picks high-clarity small bug #42 ahead of older large #40 when runs: 1.
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.settings.intake = 'active';
  w.settings.labelRequired = true;
  w.settings.label = null;
  const rOld = w.issue(40, { title: 'Old large cleanup', created: Date.parse('2026-10-01T00:00:00Z') });
  const rQuick = w.issue(42, { title: 'Crisp small bug fix', labels: ['bug'], created: Date.parse('2026-10-10T00:00:00Z') });
  await seedCardFile(w, rOld, cardByIssue[40]);
  await seedCardFile(w, rQuick, cardByIssue[42]);

  await w.tick();
  assert.deepEqual(workJobs(w).map(j => `${j.issue}:${j.role}`), ['42:build'], 'high-clarity small bug beats older large work');
});

test('active-intake 5a: bounded read-only repo-inspection auto-improve promotes improve -> ready with one comment and zero loop', async t => {
  // Unit check on improveCommand flags & token stripping.
  const codexImp = improveCommand({ kind: 'codex', command: 'codex' }, { result: '/tmp/imp.txt', model: 'gpt-5' });
  assert.equal(codexImp.args[codexImp.args.indexOf('--sandbox') + 1], 'read-only');
  assert.equal(codexImp.args.includes('--skip-git-repo-check'), false, 'runs inside real git checkout');
  assert.equal(codexImp.args.includes('--dangerously-bypass-approvals-and-sandbox'), false);
  const claudeImp = improveCommand({ kind: 'claude', command: 'claude' }, {});
  assert.equal(claudeImp.args[claudeImp.args.indexOf('--tools') + 1], 'Read,Glob,Grep');
  assert.equal(claudeImp.args[claudeImp.args.indexOf('--permission-mode') + 1], 'plan');
  assert.equal(readImprovement({ outcome: 'ready', reason: 'Missing criteria', acceptance_criteria: [] }), null, 'ready improvement requires concrete acceptance criteria');

  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.settings.intake = 'active';
  w.settings.labelRequired = true;
  w.settings.label = null;

  // Hold the 1 build slot with #50 first so we can ALSO verify zero infinite re-trigger loop across multiple ticks!
  const r50 = w.issue(50, { title: 'Slot holder', body: 'In src/holder.mjs.' });
  await seedCardFile(w, r50, { class: 'ready', reason: 'Ready holder.', confidence: 0.9, areas: ['src/holder.mjs'], size: 'medium' });
  w.issue(51, { title: 'Parser crashes on empty line', body: 'Goal is clear, needs exact file and criteria.' });

  const envWithSecrets = {
    env: {
      PATH: process.env.PATH,
      HOME: process.env.HOME,
      GH_TOKEN: 'ghs_secret_1',
      GITHUB_TOKEN: 'ghs_secret_2',
      GITHUB_PERSONAL_ACCESS_TOKEN: 'ghp_secret_3',
      OPENAI_API_KEY: 'sk-test-allowed',
    },
  };

  // Tick 1: #50 takes build slot; #51 starts initial text-only card job in empty dir.
  await w.tick(envWithSecrets);
  assert.deepEqual(workJobs(w).map(j => `${j.issue}:${j.role}`), ['50:build']);
  assert.deepEqual(intakeJobs(w).map(j => j.issue), [51]);
  assert.equal(intakeJobs(w)[0].cwd, intakeFolders(w.root).empty);

  // Card #51 returns `improve`.
  finishCard(w, 51, {
    class: 'improve',
    reason: 'Needs exact file path and acceptance criteria.',
    confidence: 0.7,
    areas: [],
    model: 'gpt-test',
  });

  // Tick 2: collectActiveIntake saves `improve` card; activeIntake launches ONE bounded repo-inspection `intake-improve` job!
  await w.tick(envWithSecrets);
  assert.equal(improveJobs(w).length, 1, 'starts one intake-improve job');
  const impJob = improveJobs(w)[0];
  assert.equal(impJob.cwd, w.cwd, 'auto-improve runs with read access to repository checkout cwd');
  assert.equal(impJob.args[impJob.args.indexOf('--sandbox') + 1], 'read-only');
  assert.equal(impJob.env.GH_TOKEN, undefined, 'zero GH_TOKEN leaked');
  assert.equal(impJob.env.GITHUB_TOKEN, undefined, 'zero GITHUB_TOKEN leaked');
  assert.equal(impJob.env.GITHUB_PERSONAL_ACCESS_TOKEN, undefined, 'zero PAT leaked');
  assert.equal(impJob.env.OPENAI_API_KEY, 'sk-test-allowed');

  finishImprove(w, 51, {
    outcome: 'ready',
    reason: 'Empty input in src/line-parser.mjs calls trim() on undefined.',
    areas: ['src/line-parser.mjs', 'test/line-parser.test.mjs'],
    reproduction: 'parseLines("") throws TypeError at src/line-parser.mjs:14.',
    acceptance_criteria: [
      'parseLines("") returns [] without throwing',
      'Unit test in test/line-parser.test.mjs covers empty string and whitespace-only lines',
    ],
    size: 'small',
    group_with: [],
    model: 'gpt-test',
  });

  // Tick 3, Tick 4, Tick 5 while #50 still holds the slot:
  // Autopilot posts ONE spec-refinement comment, promotes #51 to `ready`, and NEVER loops on its own comment!
  await w.tick(envWithSecrets);
  await w.tick(envWithSecrets);
  await w.tick(envWithSecrets);

  const c51 = w.comments(51);
  assert.equal(c51.length, 1, 'at most one spec-refinement comment posted across repeated ticks');
  assert.match(c51[0], /Autopilot inspected the repository in read-only mode and refined the specification/);
  assert.match(c51[0], /`src\/line-parser\.mjs`/);
  assert.match(c51[0], /parseLines\(""\) returns \[\] without throwing/);
  assert.match(c51[0], /<!-- pdd:autopilot-intake:improve:51:/);
  assert.equal(intakeJobs(w).filter(j => j.issue === 51).length, 1, 'no second card job triggered by own comment');
  assert.equal(improveJobs(w).filter(j => j.issue === 51).length, 1, 'no second improve job triggered by own comment');

  const savedCard51 = readIntake({ root: w.root, now: w.now() }).cards.find(c => c.issue === 51);
  assert.equal(savedCard51.card.class, 'ready');
  assert.equal(savedCard51.card.auto_improved, true);

  // Now close #50 to free the slot -> #51 immediately starts building with the refined specification in its prompt!
  w.github.close(50);
  await w.tick(envWithSecrets); // stops #50 and claims #51
  if (!workJobs(w).some(j => j.issue === 51)) await w.tick(envWithSecrets);
  const build51 = w.job(51, 'build');
  assert.ok(build51, 'promoted ready card #51 starts building');
  assert.match(build51.input, /Refined specification from Autopilot read-only repo inspection:/);
  assert.match(build51.input, /parseLines\(""\) throws TypeError at src\/line-parser\.mjs:14/);
});

test('active-intake 5b: auto-improve falls back to person + pdd:needs-decision + one concise question + alert only on genuine human decision, then resumes when answered', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.settings.intake = 'active';
  w.settings.labelRequired = true;
  w.settings.label = null;

  w.issue(52, { title: 'Add export command', body: 'Export workspace data.' });
  const alerts = [];
  const ports = { alert: async payload => { alerts.push(payload); } };

  // Tick 1 -> card job; finish as `improve`.
  await w.tick(ports);
  finishCard(w, 52, { class: 'improve', reason: 'Unclear export format contract.', confidence: 0.65 });

  // Tick 2 -> improve job; finish as `person` (genuine product/contract choice).
  await w.tick(ports);
  assert.equal(improveJobs(w).length, 1);
  finishImprove(w, 52, {
    outcome: 'person',
    reason: 'Public CLI output format is an open product contract choice.',
    areas: ['src/export.mjs'],
    question: 'Should `pdd export` emit JSON Lines or CSV by default?',
    options: ['Emit JSON Lines (.jsonl)', 'Emit CSV (.csv)'],
    recommended: 'A',
    model: 'gpt-test',
  });

  // Tick 3 & Tick 4 -> posts ONE question comment, adds pdd:needs-decision, fires ONE alert, parks without loop!
  await w.tick(ports);
  await w.tick(ports);

  assert.equal(workJobs(w).length, 0, 'parked issue is not built before human answers');
  assert.ok(w.labels(52).includes('pdd:needs-decision'), 'adds pdd:needs-decision label');
  assert.equal(w.comments(52).length, 1, 'posts exactly one concise question comment');
  assert.match(w.comments(52)[0], /> Should `pdd export` emit JSON Lines or CSV by default\?/);
  assert.match(w.comments(52)[0], /> A\) Emit JSON Lines \(\.jsonl\) \(recommended\)/);
  assert.match(w.comments(52)[0], /<!-- pdd:autopilot-core:question:52:intake-/);
  assert.equal(alerts.length, 1, 'triggers one decision alert');
  assert.equal(alerts[0].kind, 'decision');
  assert.equal(alerts[0].issue, 52);
  assert.equal(improveJobs(w).length, 1, 'does not re-run auto-improve while waiting');

  // Now a trusted human replies "A" on #52 -> Autopilot clears pdd:needs-decision, re-evaluates card with answer "A", and builds!
  w.github.comment(52, 'A', 'acme');
  await w.tick(ports); // decisionReplies removes pdd:needs-decision; activeIntake starts fresh card job with "A"
  assert.equal(w.labels(52).includes('pdd:needs-decision'), false, 'pdd:needs-decision removed after trusted reply');
  const reCardJob = [...intakeJobs(w)].reverse().find(j => j.issue === 52);
  assert.match(reCardJob.input, /"body": "A"/, 'human answer reaches re-evaluated card');

  finishCard(w, 52, { class: 'ready', reason: 'Human chose JSON Lines.', confidence: 0.95, areas: ['src/export.mjs'], size: 'small' });
  await w.tick(ports);
  const build52 = w.job(52, 'build');
  assert.ok(build52, '#52 starts building after human answer');
  assert.match(build52.input, /acme: A/, 'human answer reaches build prompt');
});

test('active-intake 6: URL host sanitization rejects spoofed github.com URLs in parseGitHubIssueUrl, issueAreas, and core linked issues', async t => {
  assert.deepEqual(parseGitHubIssueUrl('https://github.com/Acme/Widgets/issues/5'), { repository: 'acme/widgets', issue: 5 });
  assert.deepEqual(parseGitHubIssueUrl('http://GITHUB.COM/Acme/Widgets/issues/7#issuecomment-12'), { repository: 'acme/widgets', issue: 7 });
  assert.deepEqual(parseGitHubIssueUrl('github.com/acme/widgets/issues/9'), { repository: 'acme/widgets', issue: 9 });

  for (const spoofed of [
    'https://evil.example/github.com/acme/widgets/issues/5',
    'https://github.com.evil.example/acme/widgets/issues/5',
    'https://github.com@evil.example/acme/widgets/issues/5',
    'https://evil-github.com/acme/widgets/issues/5',
    'evil.example/github.com/acme/widgets/issues/5',
    'sub.github.com/acme/widgets/issues/5',
    'ftp://github.com/acme/widgets/issues/5',
  ]) {
    assert.equal(parseGitHubIssueUrl(spoofed), null, `spoofed URL rejected: ${spoofed}`);
  }

  const areas = issueAreas({
    title: 'Fix src/billing/invoice.mjs',
    body: [
      'Compare https://evil.example/github.com/org/repo/issues/5',
      'and https://github.com.evil.example/org/repo/issues/5',
      'and evil.example/github.com/org/repo/issues/5',
      'and https://github.com/org/repo/issues/5',
      'with .github/workflows/ci.yml.',
    ].join('\n'),
  });
  assert.deepEqual(areas, ['src/billing/invoice.mjs', '.github/workflows/ci.yml']);

  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(5, { title: 'Spoof target issue', body: 'SECRET_BODY_5_MUST_NOT_APPEAR' });
  w.issue(6, { title: 'Genuine target issue', body: 'REAL_LINKED_BODY_6' });
  w.issue(7, {
    title: 'Primary task',
    body: 'Ignore https://evil.example/github.com/acme/widgets/issues/5 and https://github.com.evil.example/acme/widgets/issues/5; see https://github.com/acme/widgets/issues/6.',
  });
  // Start #7 directly in intake off mode by keeping #5/#6 unready (assigned) or starting #7 with opt-in label.
  w.settings.label = 'pdd:autopilot';
  w.github.label(7, 'pdd:autopilot');
  await w.tick();
  const build7 = w.job(7, 'build');
  assert.ok(build7);
  assert.doesNotMatch(build7.input, /SECRET_BODY_5_MUST_NOT_APPEAR/, 'spoofed URL never pulls full body of #5');
  assert.match(build7.input, /REAL_LINKED_BODY_6/, 'genuine https://github.com/.../issues/6 links #6');
});

test('active-intake 7a: rebuilt cards/ or second machine sees trusted Autopilot spec-refinement comment in cardPrompt', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.settings.intake = 'active';
  w.settings.labelRequired = true;
  w.settings.label = null;

  w.issue(60, { title: 'Fix rounding glitch', body: 'Totals sometimes drift.' });
  await w.tick();
  finishCard(w, 60, { class: 'improve', reason: 'Missing file and criteria.', confidence: 0.6 });
  await w.tick();
  finishImprove(w, 60, {
    outcome: 'ready',
    reason: 'Float drift in src/calc.mjs.',
    areas: ['src/calc.mjs'],
    reproduction: '0.1 + 0.2 !== 0.3',
    acceptance_criteria: ['Round cents to integer in src/calc.mjs'],
    size: 'small',
    model: 'gpt-test',
  });

  // Wipe local intake state before core claims #60, simulating a second machine or rebuilt cards/ folder:
  // collectActiveIntake first applies the finished improve job (posting the GitHub comment), so run one observe-free
  // collection by setting runs=0 for one tick, then wipe intake/cards!
  w.settings.runs = 0;
  await w.tick();
  assert.equal(w.comments(60).length, 1);
  rmSync(intakeFolders(w.root).cards, { recursive: true, force: true });

  // Restore runs=1 and tick -> fresh card evaluation MUST receive `spec_refinement` from Autopilot's comment!
  w.settings.runs = 1;
  await w.tick();
  const freshCard = [...intakeJobs(w)].reverse().find(j => j.issue === 60);
  assert.ok(freshCard, 'fresh card job started after cards/ wipe');
  assert.match(freshCard.input, /"spec_refinement":/, 'cardPrompt includes Autopilot spec_refinement');
  assert.match(freshCard.input, /Round cents to integer in src\/calc\.mjs/);

  finishCard(w, 60, { class: 'ready', reason: 'Refined spec in comment settles scope.', confidence: 0.92, areas: ['src/calc.mjs'], size: 'small' });
  await w.tick();
  assert.ok(w.job(60, 'build'), 'second machine / rebuilt cards claims #60 cleanly');
});

test('active-intake 7b: body edit + removing pdd:needs-decision re-runs auto-improve without needing a new comment', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.settings.intake = 'active';
  w.settings.labelRequired = true;
  w.settings.label = null;

  w.issue(61, { title: 'Add export flag', body: 'Add --export to CLI.' });
  await w.tick();
  finishCard(w, 61, { class: 'improve', reason: 'Missing format.', confidence: 0.6 });
  await w.tick();
  finishImprove(w, 61, {
    outcome: 'person',
    reason: 'Format unspecified.',
    areas: ['src/export.mjs'],
    question: 'JSON or CSV?',
    options: ['JSON', 'CSV'],
    recommended: 'A',
    model: 'gpt-test',
  });
  await w.tick();
  assert.ok(w.labels(61).includes('pdd:needs-decision'));

  // Trusted author edits the issue body directly AND removes pdd:needs-decision (zero new comment!).
  w.advance(5000);
  w.github.edit(61, 'Add --export to CLI. Output format must be JSON Lines (.jsonl), exit 0.');
  w.github.unlabel(61, 'pdd:needs-decision', 'acme');

  // Tick -> fresh card runs; suppose card STILL says `improve` (needs exact repo file/criteria).
  await w.tick();
  finishCard(w, 61, { class: 'improve', reason: 'Check exact CLI file in repo.', confidence: 0.7 });

  // Next tick -> hasAutoImproveSinceHuman detects body edit and starts a new auto-improve pass instead of deadlocking!
  await w.tick();
  assert.equal(improveJobs(w).filter(j => j.issue === 61).length, 2, 'body edit allows fresh auto-improve pass');
  finishImprove(w, 61, {
    outcome: 'ready',
    reason: 'Wire --export JSONL in src/export.mjs.',
    areas: ['src/export.mjs'],
    acceptance_criteria: ['Emit JSONL when --export is passed'],
    size: 'small',
    model: 'gpt-test',
  });

  await w.tick();
  assert.ok(w.job(61, 'build'), '#61 promoted and claimed after body-edit reply');
});

test('active-intake 7c: label-only removal of pdd:needs-decision never strands issue in person and passes decision_note', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.settings.intake = 'active';
  w.settings.labelRequired = true;
  w.settings.label = null;

  w.issue(62, { title: 'Add summary flag', body: 'Add --summary flag.' });
  await w.tick();
  finishCard(w, 62, { class: 'improve', reason: 'Format open.', confidence: 0.6 });
  await w.tick();
  finishImprove(w, 62, {
    outcome: 'person',
    reason: 'Choice needed.',
    areas: ['src/summary.mjs'],
    question: 'Plain text or JSON?',
    options: ['Plain text', 'JSON'],
    recommended: 'A',
    model: 'gpt-test',
  });
  await w.tick(); // posts question + adds pdd:needs-decision
  await w.tick(); // saves native parked with previous = person card
  assert.ok(w.labels(62).includes('pdd:needs-decision'));

  // Trusted human removes ONLY pdd:needs-decision (no comment, no body edit).
  w.advance(5000);
  w.github.unlabel(62, 'pdd:needs-decision', 'acme');

  await w.tick();
  const reCard = [...intakeJobs(w)].reverse().find(j => j.issue === 62);
  assert.ok(reCard, 'label-only removal starts fresh card instead of stranding in person');
  assert.match(reCard.input, /"decision_note":/, 'cardPrompt receives trusted label-removal decision_note');

  finishCard(w, 62, { class: 'ready', reason: 'Approved recommended plain text option.', confidence: 0.9, areas: ['src/summary.mjs'], size: 'small' });
  await w.tick();
  assert.ok(w.job(62, 'build'), '#62 starts building after label-only approval');
});

test('active-intake 8: detaches companion whose claim expired or was taken over by another machine and never closes or unlabels rival companion on merge or observe', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  w.settings.intake = 'active';
  w.settings.labelRequired = true;
  w.settings.label = null;

  const r70 = w.issue(70, { title: 'Small parser fix A', body: 'Touch src/parser/token.mjs.' });
  const r71 = w.issue(71, { title: 'Small parser fix B', body: 'Touch src/parser/token.mjs.' });
  await seedCardFile(w, r70, { class: 'ready', reason: 'Small A.', confidence: 0.92, areas: ['src/parser/token.mjs'], group_with: [71], size: 'small' });
  await seedCardFile(w, r71, { class: 'ready', reason: 'Small B.', confidence: 0.91, areas: ['src/parser/token.mjs'], group_with: [70], size: 'small' });

  await w.tick();
  assert.ok(w.job(70, 'build'));
  assert.ok(w.labels(71).includes('pdd:working'));

  // Rival machine takes over companion #71 while primary #70 is running!
  w.advance(1000);
  w.github.unlabel(71, 'pdd:working', 'acme');
  w.github.claim(71, { coordinatorId: 'coord-rival', machine: 'machine-rival', actor: 'acme' });

  const { pr: pr70 } = w.build(70, { body: 'Ship parser fix A.\n\nRuntime: PASS' });
  await w.tick(); // heartbeat sees rival owns #71 and detaches #71 without touching rival's pdd:working!

  assert.ok(w.labels(71).includes('pdd:working'), 'rival pdd:working on #71 untouched by heartbeat');
  const savedJob70 = JSON.parse(readFileSync(join(w.root, 'jobs', '70.json'), 'utf8'));
  assert.equal(savedJob70.companions, undefined, 'rival-claimed companion #71 detached from job');

  w.review(70, 'PASS');
  w.suite(70, 0);
  await w.tick();

  assert.equal(pr70.merged, true, 'primary PR merged');
  assert.doesNotMatch(pr70.body, /Closes #71/, 'detached rival companion not added to closing lines');
  assert.equal(w.github.issues.get(70).state, 'closed', 'primary #70 closed on merge');
  assert.equal(w.github.issues.get(71).state, 'open', 'rival-owned companion #71 NOT closed on merge');
  assert.ok(w.labels(71).includes('pdd:working'), 'rival pdd:working on #71 untouched on merge');

  // Also test observe mode (`wouldMerge`) when rival takes over companion #73 right before wouldMerge!
  w.settings.mode = 'observe';
  const r72 = w.issue(72, { title: 'Small lexer fix A', body: 'Touch src/lexer/scan.mjs.' });
  const r73 = w.issue(73, { title: 'Small lexer fix B', body: 'Touch src/lexer/scan.mjs.' });
  await seedCardFile(w, r72, { class: 'ready', reason: 'Small lexer A.', confidence: 0.92, areas: ['src/lexer/scan.mjs'], group_with: [73], size: 'small' });
  await seedCardFile(w, r73, { class: 'ready', reason: 'Small lexer B.', confidence: 0.91, areas: ['src/lexer/scan.mjs'], group_with: [72], size: 'small' });

  await w.tick();
  w.build(72, { body: 'Ship lexer fix A.\n\nRuntime: PASS' });
  await w.tick();
  w.review(72, 'PASS');
  w.suite(72, 0);

  // Rival takes over #73 right before the observe completion tick!
  w.advance(1000);
  w.github.unlabel(73, 'pdd:working', 'acme');
  w.github.claim(73, { coordinatorId: 'coord-rival', machine: 'machine-rival', actor: 'acme' });
  await w.tick();

  assert.ok(w.labels(72).includes('pdd:would-merge'), 'primary #72 marked pdd:would-merge');
  assert.equal(w.labels(73).includes('pdd:would-merge'), false, 'rival companion #73 NOT marked pdd:would-merge');
  assert.ok(w.labels(73).includes('pdd:working'), 'rival companion #73 keeps rival pdd:working');

  // Also verify companion claim expiry (`ctx.now() - comp.claim.lastSeen >= 4h`) detaches companion cleanly!
  w.settings.mode = 'auto';
  const r74 = w.issue(74, { title: 'Small fmt fix A', body: 'Touch src/fmt/pad.mjs.' });
  const r75 = w.issue(75, { title: 'Small fmt fix B', body: 'Touch src/fmt/pad.mjs.' });
  await seedCardFile(w, r74, { class: 'ready', reason: 'Small fmt A.', confidence: 0.92, areas: ['src/fmt/pad.mjs'], group_with: [75], size: 'small' });
  await seedCardFile(w, r75, { class: 'ready', reason: 'Small fmt B.', confidence: 0.91, areas: ['src/fmt/pad.mjs'], group_with: [74], size: 'small' });
  await w.tick();
  const job74Path = join(w.root, 'jobs', '74.json');
  const job74 = JSON.parse(readFileSync(job74Path, 'utf8'));
  job74.companions[0].claim.lastSeen = w.now() - 5 * 3600_000;
  writeFileSync(job74Path, JSON.stringify(job74));
  await w.tick();
  const afterExpiry74 = JSON.parse(readFileSync(job74Path, 'utf8'));
  assert.equal(afterExpiry74.companions, undefined, 'expired companion #75 detached');
  assert.equal(w.labels(75).includes('pdd:working'), false, 'expired companion #75 pdd:working cleaned up');
});
