import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { nativeGithubCounter } from '../src/github-calls.mjs';
import { ensurePaneBudget } from '../src/workflow-chat.mjs';
import { acquireRunLock, approveRun, runStatus, startRun, stepDone, tidyRuns } from '../src/workflow-runner.mjs';
import { readablePrTop } from '../src/workflow-pr-body.mjs';
import { runPdd, renderHelp } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const saveRun = run => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));

// ---------------------------------------------------------------------------
// #3610: Inverted storyNote ternary in readableFacts + readablePrTop rendering
// ---------------------------------------------------------------------------

test('3610: readable.facts.storyNote is null when Stories are read cleanly and readablePrTop emits zero error note', async t => {
  const f = await fixture(t, { name: 'small-change' });
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  const storyDir = join(run.root, 'user_stories');
  mkdirSync(storyDir, { recursive: true });
  writeFileSync(
    join(storyDir, 'fast-status.md'),
    '# Fast status\n\nAs a developer, I want local workflow status, so that I can inspect runs offline.\n',
  );
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n');
  f.git(run.root, 'add', '.');
  f.git(run.root, 'commit', '-qm', 'update value and add story');

  // Complete each small-change area (approve gates and publish the PR).
  for (const area of run.areas) {
    for (const step of area.steps) {
      const res = await stepDone({ step, summary: `done ${step}`, cwd: run.root, packageRoot }, f.ports);
      assert.equal(res.exitCode, 0, `${area.name}/${step}: ${res.message}`);
    }
    if (area.gate === 'approve') {
      const approved = await approveRun({ ref: '17', cwd: f.source, packageRoot }, f.ports);
      assert.equal(approved.exitCode, 0, `approve ${area.name}: ${approved.message}`);
    }
  }
  const published = f.record();
  assert.equal(published.pr.length, 1, 'PR should be published');
  const facts = published.pr[0].readable?.facts;
  assert.ok(facts, 'PR should have saved readable facts');
  assert.deepEqual(facts.storyPaths, ['user_stories/fast-status.md']);
  assert.equal(facts.stories.length, 1);
  assert.strictEqual(facts.storyNote, null, 'storyNote must be strictly null when Stories were read');

  const top = readablePrTop(facts);
  assert.deepEqual(top.notes, [], 'readablePrTop must emit zero error notes when Stories are present');
  assert.match(top.text, /## User story/);
  assert.match(top.text, /As a developer, I want local workflow status/);
  assert.doesNotMatch(f.prs[0].body, /the Story file could not be read/);
});

test('3610: readable.facts.storyNote still reports unreadable Story when storyPaths exist but zero Stories can be read', async t => {
  const f = await fixture(t, { name: 'small-change' });
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  const storyDir = join(run.root, 'user_stories');
  mkdirSync(storyDir, { recursive: true });
  // A committed dangling symlink keeps the worktree clean and makes readFileSync fail across all platforms/users.
  symlinkSync('missing-story-target.md', join(storyDir, 'unreadable.md'));
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n');
  f.git(run.root, 'add', '.');
  f.git(run.root, 'commit', '-qm', 'update value with unreadable story path');

  for (const area of run.areas) {
    for (const step of area.steps) {
      const res = await stepDone({ step, summary: `done ${step}`, cwd: run.root, packageRoot }, f.ports);
      assert.equal(res.exitCode, 0, `${area.name}/${step}: ${res.message}`);
    }
    if (area.gate === 'approve') {
      const approved = await approveRun({ ref: '17', cwd: f.source, packageRoot }, f.ports);
      assert.equal(approved.exitCode, 0, `approve ${area.name}: ${approved.message}`);
    }
  }
  const published = f.record();
  const facts = published.pr[0].readable?.facts;
  assert.deepEqual(facts.storyPaths, ['user_stories/unreadable.md']);
  assert.deepEqual(facts.stories, []);
  assert.equal(facts.storyNote, 'the Story file could not be read');

  const top = readablePrTop(facts);
  assert.equal(top.notes.length, 1);
  assert.match(top.notes[0], /the Story file could not be read/);
});

// ---------------------------------------------------------------------------
// #3613: ensurePaneBudget checks paneUsage first, no double sweep on launch,
//        and tidyRuns honors localOnly, terminal-PR skip, and bounded need
// ---------------------------------------------------------------------------

test('3613: ensurePaneBudget checks paneUsage first, skips sweeps when 0 panes, and runs local-only opportunistic cleanup under budget', async () => {
  // 0 panes: zero sweeps at all.
  let paneLists = 0;
  const zeroSweeps = [];
  const empty = await ensurePaneBudget(3, {
    env: { PDD_HERDR_PANE_BUDGET: '56' },
    herdr: async args => { assert.deepEqual(args, ['pane', 'list']); paneLists++; return { result: { type: 'pane_list', panes: [] } }; },
    sweepFinished: async opts => { zeroSweeps.push(['finished', opts]); return { closed: 0, reasonCounts: {} }; },
    sweepIdle: async opts => { zeroSweeps.push(['idle', opts]); return { closed: 0, reasonCounts: {} }; },
  });
  assert.deepEqual(empty, { panes: 0, budget: 56, closed: 0 });
  assert.equal(paneLists, 1);
  assert.deepEqual(zeroSweeps, []);

  // Under budget with > 0 panes: runs local-only sweeps reusing fetched paneInventory, with 0 extra pane list calls when nothing closes.
  const panes = Array.from({ length: 5 }, (_, i) => ({
    pane_id: `p-${i}`, workspace_id: 'w-1', tab_id: `t-${i}`, terminal_id: `term-${i}`,
  }));
  paneLists = 0;
  const underBudgetCalls = [];
  const ports = {
    env: { PDD_HERDR_PANE_BUDGET: '56' },
    herdr: async args => {
      assert.deepEqual(args, ['pane', 'list']);
      paneLists++;
      return { result: { type: 'pane_list', panes } };
    },
    sweepFinished: async opts => { underBudgetCalls.push(['finished', opts]); return { closed: 0, reasonCounts: {} }; },
    sweepIdle: async opts => { underBudgetCalls.push(['idle', opts]); return { closed: 0, reasonCounts: {} }; },
  };
  const ok = await ensurePaneBudget(3, ports);
  assert.deepEqual(ok, { panes: 5, budget: 56, closed: 0 });
  assert.equal(paneLists, 1);
  assert.deepEqual(underBudgetCalls, [
    ['finished', { graceMs: 15 * 60_000, localOnly: true, paneInventory: panes }],
    ['idle', { graceMs: 60_000, localOnly: true, paneInventory: panes }],
  ]);

  // Disabled budget (0) with > 0 panes also runs only local-only opportunistic cleanup (never zero-grace or network sweeps).
  paneLists = 0;
  underBudgetCalls.length = 0;
  const disabled = await ensurePaneBudget(10, { ...ports, env: { PDD_HERDR_PANE_BUDGET: '0' } });
  assert.deepEqual(disabled, { panes: 5, budget: 0, closed: 0 });
  assert.equal(paneLists, 1);
  assert.deepEqual(underBudgetCalls, [
    ['finished', { graceMs: 15 * 60_000, localOnly: true, paneInventory: panes }],
    ['idle', { graceMs: 60_000, localOnly: true, paneInventory: panes }],
  ]);
});

test('3613: ensurePaneBudget sweeps locally with grace first under pressure, then escalates to zero grace', async () => {
  const panes = [
    { pane_id: 'p-1', workspace_id: 'w-1', tab_id: 't-1', terminal_id: 'term-1' },
    { pane_id: 'p-2', workspace_id: 'w-1', tab_id: 't-2', terminal_id: 'term-2' },
  ];
  const calls = [];
  const res = await ensurePaneBudget(1, {
    env: { PDD_HERDR_PANE_BUDGET: '2' },
    herdr: async () => ({ result: { type: 'pane_list', panes } }),
    sweepFinished: async opts => {
      calls.push(['finished', opts]);
      if (opts.graceMs === 15 * 60_000) {
        panes.pop();
        return { closed: 1, reasonCounts: {} };
      }
      return { closed: 0, reasonCounts: {} };
    },
    sweepIdle: async opts => {
      calls.push(['idle', opts]);
      return { closed: 0, reasonCounts: {} };
    },
  });
  assert.deepEqual(res, { panes: 1, budget: 2, closed: 1 });
  assert.equal(calls.length, 1);
  assert.equal(calls[0][0], 'finished');
  assert.equal(calls[0][1].graceMs, 15 * 60_000);
  assert.equal(calls[0][1].need, 1);
  assert.equal(calls[0][1].localOnly, true);
  assert.ok(Array.isArray(calls[0][1].paneInventory));

  // When normal-grace sweeps free nothing, escalate to zero-grace sweeps and fail with retained counts.
  const stuck = [{ pane_id: 'p-1', workspace_id: 'w-1', tab_id: 't-1', terminal_id: 'term-1' }];
  const escalation = [];
  await assert.rejects(
    ensurePaneBudget(1, {
      env: { PDD_HERDR_PANE_BUDGET: '1' },
      herdr: async () => ({ result: { type: 'pane_list', panes: stuck } }),
      sweepFinished: async opts => { escalation.push(['finished', opts]); return { closed: 0, reasonCounts: { 'agent-busy': 1 } }; },
      sweepIdle: async opts => { escalation.push(['idle', opts]); return { closed: 0, reasonCounts: { 'no-saved-session': 2 } }; },
    }),
    err => err.code === 'herdr_pane_budget' && /agent-busy 1/.test(err.message) && /no-saved-session 2/.test(err.message),
  );
  assert.deepEqual(escalation, [
    ['finished', { graceMs: 15 * 60_000, need: 1, localOnly: true, paneInventory: stuck }],
    ['idle', { graceMs: 60_000, need: 1, localOnly: true, paneInventory: stuck }],
    ['finished', { graceMs: 0, need: 1 }],
    ['idle', { graceMs: 0, need: 1 }],
  ]);
});

test('3613: startRun performs zero GitHub PR sweeps under budget, closes locally finished past-grace panes, and never double-sweeps', async t => {
  const f = await fixture(t);
  const baseExec = f.ports.execFile;
  const issuePorts = {
    ...f.ports,
    execFile: async (file, args, opts) => {
      const m = file === 'gh' && args[0] === 'api' && /^repos\/example\/project\/issues\/(\d+)$/.exec(args[1]);
      if (m) return { stdout: JSON.stringify({ number: Number(m[1]), html_url: `https://github.com/example/project/issues/${m[1]}`, title: `Issue ${m[1]}`, body: 'Body.' }) };
      return baseExec(file, args, opts);
    },
  };
  assert.equal((await startRun({ name: 'small-change', issue: '17', agent: 'claude', cwd: f.source, packageRoot }, issuePorts)).exitCode, 0);
  assert.equal((await startRun({ name: 'small-change', issue: '20', agent: 'claude', cwd: f.source, packageRoot }, issuePorts)).exitCode, 0);
  const commonDir = f.git(f.source, 'rev-parse', '--path-format=absolute', '--git-common-dir');
  const readN = n => JSON.parse(readFileSync(join(commonDir, 'pdd', 'runs', String(n), 'status.json'), 'utf8'));

  // Run #17: waiting with an open PR (must NOT trigger any GitHub PR sweep under budget).
  const first = readN(17);
  first.state = 'waiting';
  first.pr = [{ number: 23, url: 'https://github.com/example/project/pull/23', stage: first.areas.at(-1).name, state: 'open' }];
  saveRun(first);

  // Run #20: locally completed and past 15m grace (MUST be closed opportunistically under budget to prevent pane pileup!).
  const finished = readN(20);
  finished.state = 'completed';
  finished.chats[0].endedAt = f.clock - 20 * 60_000;
  saveRun(finished);
  f.herdr.idle();
  assert.ok(f.herdr.paneOf(finished.chats[0]), 'finished chat pane starts open');

  let prStatusReads = 0;
  const underBudgetSweeps = [];
  const ports = {
    ...issuePorts,
    env: { ...f.ports.env, PDD_HERDR_PANE_BUDGET: '56' },
    readPrStatus: async () => { prStatusReads++; return { state: 'open', ci: 'pass' }; },
    readIssueStatus: async ({ number }) => ({ number, state: 'open' }),
    sweepFinished: async opts => { underBudgetSweeps.push(['finished', opts]); return tidyRuns(opts, { ...issuePorts, readPrStatus: async () => { prStatusReads++; return { state: 'open', ci: 'pass' }; } }); },
    sweepIdle: async opts => { underBudgetSweeps.push(['idle', opts]); return { closed: 0, reasonCounts: {} }; },
  };
  const started = await startRun({ name: 'small-change', issue: '18', agent: 'claude', cwd: f.source, packageRoot }, ports);
  assert.equal(started.exitCode, 0, started.message);
  assert.equal(prStatusReads, 0, 'under-budget start must make 0 GitHub PR sweep calls');
  assert.equal(f.herdr.paneOf(finished.chats[0]), undefined, 'under-budget local-only cleanup must close locally finished past-grace pane');
  assert.equal(underBudgetSweeps.filter(([k]) => k === 'finished').length, 1, 'startChat must NOT repeat sweepFinished after pre-allocation check');
  assert.equal(underBudgetSweeps.find(([k]) => k === 'finished')[1].localOnly, true);

  // Now put an ended run under budget pressure and start issue #19: sweepFinished must run only during pre-allocation, not again inside startChat.
  const r18 = readN(18);
  r18.state = 'completed';
  r18.chats[0].endedAt = f.clock;
  saveRun(r18);
  f.herdr.idle();
  const pressureCalls = [];
  const pressurePorts = {
    ...issuePorts,
    env: { ...f.ports.env, PDD_HERDR_PANE_BUDGET: String(f.herdr.panes.length + 1) },
    sweepFinished: async opts => { pressureCalls.push(opts); return tidyRuns(opts, f.ports); },
    sweepIdle: async () => ({ closed: 0, reasonCounts: {} }),
  };
  const third = await startRun({ name: 'small-change', issue: '19', agent: 'claude', cwd: f.source, packageRoot }, pressurePorts);
  assert.equal(third.exitCode, 0, third.message);
  // Pre-allocation checks need: 3 (grace then zero-grace); startChat must NOT invoke sweepFinished with need: 1.
  assert.ok(pressureCalls.length > 0 && pressureCalls.every(c => c.need === 3), `expected only need:3 pre-allocation sweeps, got ${JSON.stringify(pressureCalls)}`);
});

test('3613: tidyRuns honors localOnly, skips terminal PRs, and stops refreshing waiting runs once need panes fit', async t => {
  const f = await fixture(t);
  const baseExec = f.ports.execFile;
  const issuePorts = {
    ...f.ports,
    execFile: async (file, args, opts) => {
      const m = file === 'gh' && args[0] === 'api' && /^repos\/example\/project\/issues\/(\d+)$/.exec(args[1]);
      if (m) return { stdout: JSON.stringify({ number: Number(m[1]), html_url: `https://github.com/example/project/issues/${m[1]}`, title: `Issue ${m[1]}`, body: 'Body.' }) };
      return baseExec(file, args, opts);
    },
  };
  for (const num of ['17', '18', '19', '20']) {
    const res = await startRun({ name: 'small-change', issue: num, agent: 'claude', cwd: f.source, packageRoot }, issuePorts);
    assert.equal(res.exitCode, 0, res.message);
  }
  const commonDir = f.git(f.source, 'rev-parse', '--path-format=absolute', '--git-common-dir');
  const readN = n => JSON.parse(readFileSync(join(commonDir, 'pdd', 'runs', String(n), 'status.json'), 'utf8'));

  // Make runs 17, 18, 19 waiting on the final area with open PRs; make run 20 waiting with a terminal merged PR.
  for (const [n, state] of [[17, 'open'], [18, 'open'], [19, 'open'], [20, 'merged']]) {
    const r = readN(n);
    r.state = 'waiting';
    r.area = r.areas.length - 1;
    r.gate = null;
    r.pr = [{ number: 100 + n, url: `https://github.com/example/project/pull/${100 + n}`, stage: r.areas.at(-1).name, state }];
    saveRun(r);
  }
  f.herdr.idle();

  // 1) localOnly: true makes ZERO GitHub calls.
  const seenLocal = [];
  await tidyRuns({ graceMs: 0, localOnly: true }, {
    ...f.ports,
    readPrStatus: async ({ url }) => { seenLocal.push(url); return { state: 'closed', ci: 'unknown' }; },
    readIssueStatus: async ({ number }) => { seenLocal.push(`issue:${number}`); return { number, state: 'open' }; },
  });
  assert.deepEqual(seenLocal, [], 'tidyRuns({ localOnly: true }) must make 0 GitHub calls');

  // 2) With need: 1 and budget = current panes, refreshing run #17 closes its PR + reclaims its panes and stops immediately without refreshing #18, #19, or terminal #20!
  const seenBounded = [];
  const budget = f.herdr.panes.length;
  const boundedRes = await tidyRuns({ graceMs: 0, need: 1 }, {
    ...f.ports,
    env: { ...f.ports.env, PDD_HERDR_PANE_BUDGET: String(budget) },
    readPrStatus: async ({ url }) => { seenBounded.push(url); return { state: 'closed', ci: 'unknown' }; },
    readIssueStatus: async ({ number }) => ({ number, state: 'open' }),
  });
  assert.equal(boundedRes.exitCode, 0);
  assert.equal(seenBounded.length, 1, `expected bounded tidy to stop after 1 newly ended run freed panes, saw: ${JSON.stringify(seenBounded)}`);
  assert.equal(new Set(seenBounded).has('https://github.com/example/project/pull/120'), false, 'terminal PR must never be refreshed');

  // 3) Explicit tidy (no need) refreshes remaining open PRs (#18, #19) but still skips terminal PR (#20).
  const seenFull = [];
  await tidyRuns({ graceMs: 0 }, {
    ...f.ports,
    readPrStatus: async ({ url }) => { seenFull.push(url); return { state: 'open', ci: 'pass' }; },
    readIssueStatus: async ({ number }) => ({ number, state: 'open' }),
  });
  assert.equal(new Set(seenFull).has('https://github.com/example/project/pull/120'), false, 'terminal PR #120 must be skipped');
  assert.equal(seenFull.length, 2, `expected exactly 2 open PR refreshes, got ${JSON.stringify(seenFull)}`);
});

// ---------------------------------------------------------------------------
// #3614 + #3578 (--local): memoized findCostRun, bounded concurrent listStatus,
//                          single Herdr snapshot, and `pdd workflow status --local`
// ---------------------------------------------------------------------------

test('3614: nativeGithubCounter memoizes git rev-parse and runs/ scan per resolved cwd', async t => {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-cost-memo-')));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const repo = join(dir, 'repo');
  const worktree = join(dir, 'wt-17');
  mkdirSync(repo);
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: repo });
  const commonDir = realpathSync(join(repo, '.git'));
  const runDir = join(commonDir, 'pdd', 'runs', '17');
  mkdirSync(runDir, { recursive: true });
  mkdirSync(join(worktree, '.git'), { recursive: true });
  writeFileSync(join(runDir, 'status.json'), JSON.stringify({ root: worktree, runDir }));

  let gitRevParseCount = 0;
  let readdirRunsCount = 0;
  const recorded = [];
  let failOnce = true;

  const fsWrapper = {
    existsSync: p => {
      if (p.endsWith('.git')) return p === join(worktree, '.git') || p === join(repo, '.git');
      return false;
    },
    readdirSync: p => {
      if (p === join(commonDir, 'pdd', 'runs')) {
        readdirRunsCount++;
        return ['17'];
      }
      throw Object.assign(Error('ENOENT'), { code: 'ENOENT' });
    },
    readFileSync: (p, enc) => readFileSync(p, enc),
  };

  const counted = nativeGithubCounter(
    async (file, args, opts) => {
      if (file === 'git' && args[0] === 'rev-parse') {
        gitRevParseCount++;
        if (failOnce && opts.cwd === repo) {
          failOnce = false;
          throw Error('transient git error');
        }
        return { stdout: `${commonDir}\n` };
      }
      return { stdout: 'HTTP/2.0 200\r\n\r\n{}' };
    },
    {
      fs: fsWrapper,
      now: () => 1_700_000_000_000,
      costRecord: (dirPath, entry) => recorded.push({ dirPath, entry }),
    },
  );

  // 50 gh calls in the same worktree (including non-normalized `/wt-17/.` path): 1 git rev-parse + 1 runs/ scan!
  await Promise.all(Array.from({ length: 50 }, (_, i) =>
    counted('gh', ['api', `repos/example/project/issues/${i + 1}`], { cwd: i % 2 === 0 ? worktree : join(worktree, '.') }),
  ));
  assert.equal(gitRevParseCount, 1, '50 gh calls must spawn only 1 git rev-parse');
  assert.equal(readdirRunsCount, 1, '50 gh calls must scan runs/ only once');
  assert.equal(recorded.length, 50);
  assert.ok(recorded.every(r => r.dirPath === runDir));

  // Transient git failure for another cwd must not poison the cache and must keep gh result intact.
  const firstRepoCall = await counted('gh', ['api', 'repos/example/project/issues/1'], { cwd: repo });
  assert.ok(firstRepoCall.stdout.includes('200'));
  assert.equal(gitRevParseCount, 2);
  await counted('gh', ['api', 'repos/example/project/issues/2'], { cwd: repo });
  await counted('gh', ['api', 'repos/example/project/issues/3'], { cwd: repo });
  assert.equal(gitRevParseCount, 3, 'retry after transient error succeeds and caches subsequent calls');
  assert.equal(readdirRunsCount, 2);

  // Explicit costRun override port runs directly on every gh call unchanged.
  let overrideCalls = 0;
  const withOverride = nativeGithubCounter(
    async () => ({ stdout: 'HTTP/2.0 200\r\n\r\n{}' }),
    {
      costRun: async () => { overrideCalls++; return runDir; },
      costRecord: () => {},
    },
  );
  await withOverride('gh', ['api', 'repos/example/project/issues/1'], { cwd: worktree });
  await withOverride('gh', ['api', 'repos/example/project/issues/2'], { cwd: worktree });
  assert.equal(overrideCalls, 2);
});

test('3614: listStatus skips terminal PRs, refreshes open waiting PRs with bounded concurrency (<= 6), and shares one Herdr snapshot', async t => {
  const f = await fixture(t);
  const baseExec = f.ports.execFile;
  const issuePorts = {
    ...f.ports,
    execFile: async (file, args, opts) => {
      const m = file === 'gh' && args[0] === 'api' && /^repos\/example\/project\/issues\/(\d+)$/.exec(args[1]);
      if (m) return { stdout: JSON.stringify({ number: Number(m[1]), html_url: `https://github.com/example/project/issues/${m[1]}`, title: `Issue ${m[1]}`, body: 'Body.' }) };
      return baseExec(file, args, opts);
    },
  };
  const issueNumbers = [17, 18, 19, 20, 21, 22, 23, 24, 25, 26];
  for (const n of issueNumbers) {
    const res = await startRun({ name: 'small-change', issue: String(n), agent: 'claude', cwd: f.source, packageRoot }, issuePorts);
    assert.equal(res.exitCode, 0, res.message);
  }
  const commonDir = f.git(f.source, 'rev-parse', '--path-format=absolute', '--git-common-dir');
  const readN = n => JSON.parse(readFileSync(join(commonDir, 'pdd', 'runs', String(n), 'status.json'), 'utf8'));

  // 8 open PRs (#17..#24) + 1 merged PR (#25) + 1 locally reconcilable closed final-area PR (#26).
  for (const n of issueNumbers) {
    const r = readN(n);
    r.state = 'waiting';
    r.area = r.areas.length - 1;
    r.gate = null;
    r.pr = [{
      number: 200 + n,
      url: `https://github.com/example/project/pull/${200 + n}`,
      stage: r.areas.at(-1).name,
      state: n === 25 ? 'merged' : n === 26 ? 'closed' : 'open',
    }];
    saveRun(r);
  }
  // Mark one additional finished chat on #17 past grace so closeFinishedChats({ dryRun: true }) exercises cached inventory too.
  const r17 = readN(17);
  r17.chats[0].endedAt = f.clock - 20 * 60_000;
  r17.state = 'waiting';
  saveRun(r17);
  f.herdr.idle();
  f.herdr.calls.length = 0;

  let active = 0;
  let maxActive = 0;
  const seenPrUrls = [];
  const messages = [];
  const res = await runStatus({ cwd: f.source, json: true }, {
    ...f.ports,
    say: line => messages.push(line),
    readPrStatus: async ({ url }) => {
      seenPrUrls.push(url);
      active++;
      maxActive = Math.max(maxActive, active);
      await new Promise(resolve => setTimeout(resolve, 15));
      active--;
      return { state: 'open', ci: 'pass' };
    },
    readIssueStatus: async ({ number }) => ({ number, state: 'open' }),
  });
  assert.equal(res.exitCode, 0, res.message);
  assert.equal(seenPrUrls.length, 8, `expected 8 open PR refreshes (skipping 2 terminal PRs), saw ${seenPrUrls.length}`);
  const seenPrSet = new Set(seenPrUrls);
  assert.equal(seenPrSet.has('https://github.com/example/project/pull/225'), false, 'merged PR must be skipped');
  assert.equal(seenPrSet.has('https://github.com/example/project/pull/226'), false, 'closed PR must be skipped');
  assert.ok(maxActive > 1, `expected concurrent PR refreshes (maxActive > 1), got ${maxActive}`);
  assert.ok(maxActive <= 6, `expected bounded concurrency <= 6, got ${maxActive}`);
  assert.ok(messages.includes('Reading 8 PRs from GitHub…'), `expected progress line for 8 non-terminal PRs, got ${JSON.stringify(messages)}`);

  const paneListCalls = f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'list');
  const workspaceListCalls = f.herdr.calls.filter(args => args[0] === 'workspace' && args[1] === 'list');
  assert.equal(paneListCalls.length, 1, `expected exactly 1 Herdr pane list snapshot across 10 runs, got ${paneListCalls.length}`);
  assert.ok(workspaceListCalls.length <= 1, `expected at most 1 Herdr workspace list snapshot across 10 runs, got ${workspaceListCalls.length}`);

  // Verify runBounded settles all in-flight workers before rejecting on workflow_run_save_failed and stops dispatching remaining items.
  const saveErr = Object.assign(Error('disk full'), { code: 'workflow_run_save_failed' });
  let startedWorkers = 0;
  let activeWorkers = 0;
  const failRes = await runStatus({ cwd: f.source, json: true }, {
    ...f.ports,
    readPrStatus: async () => {
      const idx = ++startedWorkers;
      activeWorkers++;
      if (idx === 1) {
        await new Promise(resolve => setTimeout(resolve, 5));
        activeWorkers--;
        throw saveErr;
      }
      await new Promise(resolve => setTimeout(resolve, 25));
      activeWorkers--;
      return { state: 'open', ci: 'pass' };
    },
    readIssueStatus: async ({ number }) => ({ number, state: 'open' }),
  });
  assert.notEqual(failRes.exitCode, 0, 'non-busy workflow_run_save_failed must propagate out of concurrent pool');
  assert.equal(activeWorkers, 0, 'all in-flight workers must have settled before rejection (no detached writes)');
  assert.ok(startedWorkers <= 6, `bounded pool must stop taking new items after fatal error (started ${startedWorkers} of 8)`);
});

test('3614: refreshPr skips merged PRs on multi-PR runs but still re-checks closed PRs (which can be reopened/merged)', async t => {
  const f = await fixture(t, { name: 'bug' });
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.state = 'waiting';
  run.pr = [
    { number: 301, url: 'https://github.com/example/project/pull/301', stage: run.areas[0].name, state: 'merged', ci: 'passing' },
    { number: 302, url: 'https://github.com/example/project/pull/302', stage: run.areas.at(-1).name, state: 'open', ci: 'pending' },
  ];
  saveRun(run);

  const fetched = [];
  const said = [];
  const res = await runStatus({ ref: '17', cwd: f.source, json: true }, {
    ...f.ports,
    say: line => said.push(line),
    readPrStatus: async ({ url }) => { fetched.push(url); return { state: 'open', ci: 'passing' }; },
    readIssueStatus: async ({ number }) => ({ number, state: 'open' }),
  });
  assert.equal(res.exitCode, 0, res.message);
  assert.deepEqual(fetched, ['https://github.com/example/project/pull/302'], 'refreshPr must skip already-merged PR 1 and only fetch open PR 2');
  assert.deepEqual(said, ['Reading the PR from GitHub…']);

  // A saved `closed` PR (e.g. ask-code with through: 'code') can be reopened and merged on GitHub, so single-run refreshPr must re-check it.
  const closedRun = f.record();
  closedRun.state = 'waiting';
  closedRun.through = 'code';
  closedRun.gate = { area: closedRun.areas[0].name, kind: 'ask-code', at: f.clock };
  closedRun.pr = [
    { number: 301, url: 'https://github.com/example/project/pull/301', stage: closedRun.areas[0].name, state: 'closed', ci: 'none' },
  ];
  saveRun(closedRun);
  const rechecked = [];
  const reopenedRes = await runStatus({ ref: '17', cwd: f.source, json: true }, {
    ...f.ports,
    readPrStatus: async ({ url }) => { rechecked.push(url); return { state: 'merged', ci: 'passing' }; },
    readIssueStatus: async ({ number }) => ({ number, state: 'open' }),
  });
  assert.equal(reopenedRes.exitCode, 0, reopenedRes.message);
  assert.deepEqual(rechecked, ['https://github.com/example/project/pull/301'], 'single-run refreshPr must still re-check a saved closed PR');
  assert.equal(f.record().pr[0].state, 'merged');
});

test('3614: nativeGithubCounter detects newly created status.json later in the same process with 0 extra git rev-parse calls', async t => {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-cost-late-status-')));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const repo = join(dir, 'repo');
  const worktree = join(dir, 'wt-17');
  mkdirSync(repo);
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: repo });
  const commonDir = realpathSync(join(repo, '.git'));
  mkdirSync(join(worktree, '.git'), { recursive: true });

  let gitRevParseCount = 0;
  const recorded = [];
  const counted = nativeGithubCounter(
    async (file, args) => {
      if (file === 'git' && args[0] === 'rev-parse') {
        gitRevParseCount++;
        return { stdout: `${commonDir}\n` };
      }
      return { stdout: 'HTTP/2.0 200\r\n\r\n{}' };
    },
    {
      now: () => 1_700_000_000_000,
      costRecord: (dirPath, entry) => recorded.push({ dirPath, entry }),
    },
  );

  // Calls 1 & 2 happen before runs/17/status.json exists -> null result, 1 git rev-parse.
  await counted('gh', ['api', 'repos/example/project/issues/17'], { cwd: worktree });
  await counted('gh', ['api', 'repos/example/project/issues/17'], { cwd: worktree });
  assert.equal(gitRevParseCount, 1);
  assert.equal(recorded.length, 0);

  // Now create runs/17/status.json on disk in the same long-lived process.
  const runDir = join(commonDir, 'pdd', 'runs', '17');
  mkdirSync(runDir, { recursive: true });
  writeFileSync(join(runDir, 'status.json'), JSON.stringify({ root: worktree, runDir }));

  // Subsequent calls attribute cost to runDir with 0 extra git rev-parse calls!
  for (let i = 0; i < 5; i++) {
    await counted('gh', ['api', `repos/example/project/issues/${i + 1}`], { cwd: worktree });
  }
  assert.equal(gitRevParseCount, 1, 'must NOT re-spawn git rev-parse when runs/ changes');
  assert.equal(recorded.length, 5, 'all post-creation gh calls must be attributed to the new runDir');
  assert.ok(recorded.every(r => r.dirPath === runDir));
});

test('3614: nativeGithubCounter handles synchronous exec doubles and never caches non-zero or empty git rev-parse replies', async t => {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-cost-sync-exec-')));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const repo = join(dir, 'repo');
  const worktree = join(dir, 'wt-17');
  mkdirSync(repo);
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: repo });
  const commonDir = realpathSync(join(repo, '.git'));
  const runDir = join(commonDir, 'pdd', 'runs', '17');
  mkdirSync(runDir, { recursive: true });
  mkdirSync(join(worktree, '.git'), { recursive: true });
  writeFileSync(join(runDir, 'status.json'), JSON.stringify({ root: worktree, runDir }));

  let gitCalls = 0;
  const recorded = [];
  // Synchronous (non-Promise) exec test double: 1st call returns non-zero code, 2nd returns empty stdout, 3rd succeeds!
  const counted = nativeGithubCounter(
    (file, args) => {
      if (file === 'git' && args[0] === 'rev-parse') {
        gitCalls++;
        if (gitCalls === 1) return { stdout: '', code: 128 };
        if (gitCalls === 2) return { stdout: '   \n', code: 0 };
        return { stdout: `${commonDir}\n`, code: 0 };
      }
      return { stdout: 'HTTP/2.0 200\r\n\r\n{}', code: 0 };
    },
    {
      now: () => 1_700_000_000_000,
      costRecord: (dirPath, entry) => recorded.push({ dirPath, entry }),
    },
  );

  await counted('gh', ['api', 'repos/example/project/issues/1'], { cwd: worktree });
  assert.equal(gitCalls, 1);
  assert.equal(recorded.length, 0, 'non-zero git rev-parse must not cache or attribute');

  await counted('gh', ['api', 'repos/example/project/issues/2'], { cwd: worktree });
  assert.equal(gitCalls, 2);
  assert.equal(recorded.length, 0, 'empty stdout git rev-parse must not cache or attribute');

  await counted('gh', ['api', 'repos/example/project/issues/3'], { cwd: worktree });
  await counted('gh', ['api', 'repos/example/project/issues/4'], { cwd: worktree });
  assert.equal(gitCalls, 3, 'once valid commonDir succeeds, subsequent calls reuse cached commonDir');
  assert.equal(recorded.length, 2);
  assert.ok(recorded.every(r => r.dirPath === runDir));
});

test('3614: listStatus locally reconciles a waiting run with a saved closed final-area PR with 0 GitHub calls', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.state = 'waiting';
  run.area = run.areas.length - 1;
  run.gate = null;
  run.pr = [{ number: 401, url: 'https://github.com/example/project/pull/401', stage: run.areas.at(-1).name, state: 'closed' }];
  saveRun(run);

  let ghCalls = 0;
  const res = await runStatus({ cwd: f.source, cancelled: true, json: true }, {
    ...f.ports,
    readPrStatus: async () => { ghCalls++; return { state: 'closed', ci: 'unknown' }; },
    readIssueStatus: async () => { ghCalls++; return { number: 17, state: 'open' }; },
  });
  assert.equal(res.exitCode, 0, res.message);
  assert.equal(ghCalls, 0, 'reconciling a saved closed final-area PR must make 0 GitHub calls');
  const data = JSON.parse(res.message);
  assert.equal(data.runs.length, 1);
  assert.equal(data.runs[0].group, 'cancelled');
  assert.equal(data.runs[0].words, 'cancelled');
  assert.equal(f.record().state, 'cancelled');
  assert.equal(f.record().cancelled?.reason, 'pr-closed');
});

test('3614: listStatus makes 0 GitHub calls for a locally reconcilable closedWaitingReason run even under run_busy lock contention', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.state = 'waiting';
  run.area = run.areas.length - 1;
  run.gate = null;
  run.pr = [{ number: 402, url: 'https://github.com/example/project/pull/402', stage: run.areas.at(-1).name, state: 'closed' }];
  saveRun(run);

  let ghCalls = 0;
  const said = [];
  const release = acquireRunLock(run.runDir);
  try {
    const res = await runStatus({ cwd: f.source, json: true }, {
      ...f.ports,
      say: line => said.push(line),
      readPrStatus: async () => { ghCalls++; return { state: 'closed', ci: 'unknown' }; },
      readIssueStatus: async () => { ghCalls++; return { number: 17, state: 'open' }; },
    });
    assert.equal(res.exitCode, 0, res.message);
  } finally {
    release();
  }
  assert.equal(ghCalls, 0, 'run_busy lock contention on a closedWaitingReason run must NOT fall through to GitHub');
  assert.deepEqual(said, [], 'locally reconcilable closedWaitingReason run must not emit a GitHub PR-reading progress line');
});

test('3614: listStatus and tidyRuns re-check a closed PR on an active non-reconcilable run (ask-code with through: code) while skipping merged PRs', async t => {
  const f = await fixture(t, { name: 'bug' });
  assert.equal((await f.run()).exitCode, 0);
  const askArea = f.record().areas.find(a => a.then === 'ask-code');
  assert.ok(askArea, 'bug workflow must have an ask-code area');

  const resetActiveClosed = () => {
    const run = f.record();
    run.state = 'waiting';
    run.area = run.areas.indexOf(askArea);
    run.through = 'code';
    run.gate = { area: askArea.name, kind: 'ask-code', at: f.clock };
    run.pr = [
      { number: 501, url: 'https://github.com/example/project/pull/501', stage: askArea.name, state: 'closed', ci: 'none' },
    ];
    saveRun(run);
  };

  // 1) listStatus re-checks the active non-reconcilable closed PR and picks up its reopened+merged state.
  resetActiveClosed();
  const listFetched = [];
  const listSaid = [];
  const listRes = await runStatus({ cwd: f.source, json: true }, {
    ...f.ports,
    say: line => listSaid.push(line),
    readPrStatus: async ({ url }) => { listFetched.push(url); return { state: 'merged', ci: 'passing' }; },
    readIssueStatus: async ({ number }) => ({ number, state: 'open' }),
  });
  assert.equal(listRes.exitCode, 0, listRes.message);
  assert.deepEqual(listFetched, ['https://github.com/example/project/pull/501']);
  assert.deepEqual(listSaid, ['Reading 1 PR from GitHub…']);
  assert.equal(f.record().pr[0].state, 'merged');
  assert.equal(f.record().doneAt, 'PR 1');

  // Once merged, a subsequent listStatus makes 0 PR calls.
  const afterMerged = [];
  await runStatus({ cwd: f.source, json: true }, {
    ...f.ports,
    readPrStatus: async ({ url }) => { afterMerged.push(url); return { state: 'merged', ci: 'passing' }; },
    readIssueStatus: async ({ number }) => ({ number, state: 'open' }),
  });
  assert.deepEqual(afterMerged, []);

  // 2) tidyRuns also re-checks the active non-reconcilable closed PR (and skips once merged).
  resetActiveClosed();
  const tidyFetched = [];
  const tidyRes = await tidyRuns({ graceMs: 0 }, {
    ...f.ports,
    readPrStatus: async ({ url }) => { tidyFetched.push(url); return { state: 'merged', ci: 'passing' }; },
    readIssueStatus: async ({ number }) => ({ number, state: 'open' }),
  });
  assert.equal(tidyRes.exitCode, 0);
  assert.deepEqual(tidyFetched, ['https://github.com/example/project/pull/501']);
  assert.equal(f.record().pr[0].state, 'merged');
});

test('3578 / 3614: pdd workflow status --local parses, appears in help, dispatches local: true, and makes 0 gh and 0 herdr calls', async t => {
  // 1) Catalog parsing & help text
  const parsed = parseArgv(['workflow', 'status', '--local', '--all', '--json']);
  assert.equal(parsed.commandId, 'workflow.status');
  assert.equal(parsed.options['--local'], true);
  assert.equal(parsed.options['--all'], true);
  assert.equal(parsed.options['--json'], true);
  const help = renderHelp(['workflow', 'status'], packageRoot);
  assert.match(help, /--local/);
  assert.match(help, /no GitHub or Herdr calls/i);

  // 2) CLI dispatch forwards `local: true` only when `--local` is supplied.
  const dispatched = [];
  const sink = { write() {} };
  const codeWith = await runPdd(['workflow', 'status', '--local', '--json'], {
    cwd: packageRoot, stdout: sink, stderr: sink, packageRoot,
    workflowRunner: { runStatus: async args => { dispatched.push(args); return { exitCode: 0, message: '{"runs":[]}' }; } },
  });
  assert.equal(codeWith, 0);
  assert.equal(dispatched[0].local, true);
  assert.equal(dispatched[0].json, true);

  const codeWithout = await runPdd(['workflow', 'status'], {
    cwd: packageRoot, stdout: sink, stderr: sink, packageRoot,
    workflowRunner: { runStatus: async args => { dispatched.push(args); return { exitCode: 0, message: 'ok' }; } },
  });
  assert.equal(codeWithout, 0);
  assert.equal(Object.hasOwn(dispatched[1], 'local'), false, 'omitting --local must not inject local property');

  // 3) End-to-end runStatus({ local: true }) in BOTH list mode and single-run detail mode: 0 gh, 0 herdr, 0 GitHub progress lines.
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.state = 'waiting';
  run.pr = [{ number: 23, url: 'https://github.com/example/project/pull/23', stage: 'change', state: 'open' }];
  saveRun(run);

  const unexpectedCalls = [];
  const said = [];
  const baseExec = f.ports.execFile;
  const offlinePorts = {
    ...f.ports,
    say: text => said.push(text),
    herdr: async args => { unexpectedCalls.push(['herdr', ...args]); throw Error('herdr must not be called with --local'); },
    readPrStatus: async args => { unexpectedCalls.push(['readPrStatus', args.url]); throw Error('gh must not be called with --local'); },
    readIssueStatus: async args => { unexpectedCalls.push(['readIssueStatus', args.number]); throw Error('gh must not be called with --local'); },
    execFile: async (file, args, opts) => {
      if (file === 'gh') { unexpectedCalls.push(['gh', ...args]); throw Error('gh must not be called with --local'); }
      return baseExec(file, args, opts);
    },
  };

  const listResult = await runStatus({ cwd: f.source, local: true, json: true }, offlinePorts);
  assert.equal(listResult.exitCode, 0, listResult.message);
  const listData = JSON.parse(listResult.message);
  assert.equal(listData.herdr, null);
  assert.equal(listData.runs.length, 1);
  assert.equal(listData.runs[0].number, 17);

  const detailJson = await runStatus({ ref: '17', cwd: f.source, local: true, json: true }, offlinePorts);
  assert.equal(detailJson.exitCode, 0, detailJson.message);
  const detailData = JSON.parse(detailJson.message);
  assert.equal(detailData.runs.length, 1);
  assert.equal(detailData.runs[0].number, 17);

  const detailText = await runStatus({ ref: '17', cwd: f.source, local: true }, offlinePorts);
  assert.equal(detailText.exitCode, 0, detailText.message);
  assert.match(detailText.message, /example\/project#17/);
  assert.doesNotMatch(detailText.message, /Reading .* from GitHub/);

  const worktreeText = await runStatus({ cwd: run.root, local: true }, offlinePorts);
  assert.equal(worktreeText.exitCode, 0, worktreeText.message);
  assert.match(worktreeText.message, /example\/project#17/);

  assert.deepEqual(unexpectedCalls, [], `expected 0 gh and 0 herdr calls under --local, saw ${JSON.stringify(unexpectedCalls)}`);
  assert.deepEqual(said, [], `expected 0 GitHub progress messages under --local, saw ${JSON.stringify(said)}`);
});
