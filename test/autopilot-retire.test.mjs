import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import { existsSync, mkdtempSync, mkdirSync, rmSync, writeFileSync, readFileSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { moveToCore, movedState, engineBefore, oldProcessOf, parseProcesses, procTable, claimRecord, RETIRED_NOTE, MAX_DEFERS, FULL_ENGINE_REMOVED } from '../src/autopilot-retire.mjs';
import { coreWorld } from './helpers/core-world.mjs';

const REPO = 'acme/widgets', UID = 501, ME = { coordinatorId: 'coord-a', machine: 'host-a' }, OTHER = { coordinatorId: 'coord-b', machine: 'host-b' };
const claimBody = (who, labelEventId) => `Autopilot claim.\n\n\`\`\`json\n${JSON.stringify({ repository: REPO, ...who, labelEventId: String(labelEventId), lastSeen: '' })}\n\`\`\``;

// A small GitHub: issues with labels, comments and label events; PRs with a state and comments. Every write is kept.
function fakeGithub() {
  const g = { issues: new Map(), pulls: new Map(), writes: [], fail: null, nextId: 100 };
  g.issue = (n, { labels = [], comments = [], timeline = [] } = {}) => { g.issues.set(n, { number: n, labels: [...labels], comments: comments.map(c => ({ id: g.nextId++, ...c })), timeline }); return g.issues.get(n); };
  g.claim = (n, who, { labels = [] } = {}) => { const event = g.nextId++; return g.issue(n, { labels: ['pdd:working', ...labels], timeline: [{ id: event, event: 'labeled', label: { name: 'pdd:working' } }], comments: [{ body: claimBody(who, event) }] }); };
  g.pull = (n, { state = 'open', merged = false } = {}) => { g.pulls.set(n, { number: n, state, merged, comments: [] }); };
  const reply = (status, value) => ({ code: 0, stdout: `HTTP/2.0 ${status} X\r\n\r\n${value === undefined ? '' : JSON.stringify(value)}` });
  g.gh = async (args, options = {}) => {
    const method = args[args.indexOf('--method') + 1], endpoint = args[args.indexOf('--method') + 2];
    if (g.fail?.(method, endpoint)) return reply(502, { message: 'Bad Gateway' });
    const input = options.input ? JSON.parse(options.input) : undefined;
    if (method !== 'GET') g.writes.push([method, endpoint, input]);
    const path = endpoint.replace(`repos/${REPO}/`, '').split('?')[0];
    let m;
    if (path === 'issues' && method === 'GET') return reply(200, [...g.issues.values()].filter(i => i.labels.includes('pdd:working')).map(i => ({ number: i.number, labels: i.labels.map(name => ({ name })) })));
    if ((m = /^issues\/comments\/(\d+)$/.exec(path)) && method === 'DELETE') {
      for (const holder of [...g.issues.values(), ...g.pulls.values()]) { const at = holder.comments.findIndex(c => c.id === Number(m[1])); if (at >= 0) { holder.comments.splice(at, 1); return reply(204); } }
      return reply(404, { message: 'Not Found' });
    }
    if ((m = /^pulls\/(\d+)$/.exec(path))) { const pr = g.pulls.get(Number(m[1])); return pr ? reply(200, { number: pr.number, state: pr.state, merged: pr.merged }) : reply(404, {}); }
    if ((m = /^issues\/(\d+)(\/.*)?$/.exec(path))) {
      const n = Number(m[1]), sub = m[2] ?? '', holder = g.issues.get(n) ?? g.pulls.get(n);
      if (!holder) return reply(404, { message: 'Not Found' });
      if (sub === '' && method === 'GET') return reply(200, { number: n, labels: (holder.labels ?? []).map(name => ({ name })) });
      if (sub === '/comments' && method === 'GET') return reply(200, holder.comments);
      if (sub === '/comments' && method === 'POST') { holder.comments.push({ id: g.nextId++, body: input.body }); return reply(201, {}); }
      if (sub === '/timeline') return reply(200, holder.timeline ?? []);
      if ((m = /^\/labels\/(.+)$/.exec(sub)) && method === 'DELETE') {
        const name = decodeURIComponent(m[1]); if (!holder.labels.includes(name)) return reply(404, {});
        holder.labels = holder.labels.filter(x => x !== name); holder.timeline.push({ id: g.nextId++, event: 'unlabeled', label: { name } }); return reply(200, []);
      }
    }
    return reply(404, { message: 'Not Found' });
  };
  return g;
}

const run = (number, who, { state = 'running', prs = [], runDir = `/repo/.git/pdd/runs/${number}` } = {}) => ({ number, repo: REPO, state, runId: `run-${number}`, sourceRoot: '/repo', root: `/repo.pdd-worktrees/${number}`, runDir,
  automaticOrigin: { repository: REPO, ...who, claim: { commentId: 'unknown', labelEventId: 'unknown' } }, pr: prs.map(number => ({ number })) });

// The machine of the old full engine: a coordinator pane, 2 live runs with claims, PR 1 and PR 2, a cancelled run's
// closed PR, and old completion workers. Another machine has its own claim, run and PR.
function fullWorld() {
  const g = fakeGithub(), w = { g, herdrCalls: [], cancelled: [], released: [], signals: [], saves: [], now: 1_000_000 };
  const a = g.claim(11, ME), b = g.claim(12, ME, { labels: ['pdd:needs-decision', 'pdd:stuck', 'area:docs'] }), c = g.claim(13, OTHER);
  g.pull(21); g.pull(22); g.pull(23, { state: 'closed' }); g.pull(31);
  w.runs = [run(11, ME, { prs: [21] }), run(12, ME, { prs: [22] }), run(9, ME, { state: 'cancelled', prs: [23], runDir: '/repo/.git/pdd/runs/9-cancelled-abcd1234' }), run(13, OTHER, { prs: [31] })];
  w.runs[0].automaticOrigin.claim = { commentId: String(a.comments[0].id), labelEventId: String(a.timeline[0].id) };
  w.runs[1].automaticOrigin.claim = { commentId: String(b.comments[0].id), labelEventId: String(b.timeline[0].id) };
  w.claimC = c.comments[0].id;
  w.panes = new Map([['pane-1', { pane_id: 'pane-1', workspace_id: 'ws-1', cwd: '/repo', agent: 'codex', agent_status: 'idle' }]]);
  w.procs = [
    { pid: 501, ppid: 1, pgid: 501, rss: 51200, start: 'Mon Nov 11 10:00:01 2026', args: `node /pkg/src/workflow-worker-completion.mjs ${JSON.stringify({ runId: 'r1', runDir: '/repo/.git/pdd/runs/11', sourceRoot: '/repo' })}` },
    { pid: 502, ppid: 1, pgid: 502, rss: 51200, start: 'Mon Nov 11 10:00:02 2026', args: `node /pkg/src/workflow-worker-completion.mjs ${JSON.stringify({ runId: 'r0', runDir: '/repo/.git/pdd/runs/9-cancelled-abcd1234', sourceRoot: '/repo' })}`, stubborn: true },
    { pid: 503, ppid: 1, pgid: 503, rss: 1024, start: 'Mon Nov 11 10:00:03 2026', args: `node /pkg/src/autopilot-launcher.mjs --coordinator-idle ${JSON.stringify({ stateFile: '/state/a.json', paneId: 'pane-1' })}` },
    { pid: 601, ppid: 1, pgid: 601, rss: 51200, start: 'Mon Nov 11 10:00:04 2026', args: `node /pkg/src/workflow-worker-completion.mjs ${JSON.stringify({ runId: 'x', runDir: '/other/.git/pdd/runs/3', sourceRoot: '/other' })}` },
    { pid: 602, ppid: 1, pgid: 602, rss: 2048, start: 'Mon Nov 11 10:00:05 2026', args: 'node /pkg/src/autopilot-launcher.mjs --start-scan-wait {"stateFile":"/state/a.json"}' },
    { pid: 603, ppid: 1, pgid: 603, rss: 2048, start: 'Mon Nov 11 10:00:06 2026', args: 'vim notes.txt' },
  ];
  w.state = { repo: REPO, cwd: '/repo', ...ME, paneId: 'pane-1', workspaceId: 'ws-1', agent: { kind: 'codex', id: 'codex' }, ownerLaunch: { profile: { agent: { id: 'codex', kind: 'codex' } } },
    githubIntake: { claims: [{ issue: `https://github.com/${REPO}/issues/11`, ...ME, owner: ME.coordinatorId }] }, parking: { a: 1 }, recipeDelivered: true, enabled: true };
  const gone = code => Object.assign(Error(code), { code });
  w.ports = {
    now: () => w.now, commonDir: '/repo/.git', samePath: (x, y) => x === y, coreJobs: () => new Set(), gh: g.gh,
    save: journal => { w.saves.push(structuredClone(journal)); },
    herdr: async args => {
      w.herdrCalls.push(args.join(' '));
      const pane = w.panes.get(args[2]);
      if (args[0] === 'agent' && args[1] === 'get') { if (!pane) throw gone('agent_not_found'); return { result: { agent: pane } }; }
      if (args[0] === 'pane' && args[1] === 'close') { w.panes.delete(args[2]); return { result: {} }; }
      if (args[0] === 'pane' && args[1] === 'get') { if (!pane) throw gone('pane_not_found'); return { result: { pane } }; }
      throw gone('unknown');
    },
    listRuns: async (cancelled = false) => w.runs.filter(r => cancelled || r.state !== 'cancelled'),
    cancelRun: async r => { w.cancelled.push(r.number); r.state = 'cancelled'; return { exitCode: 0, message: 'Cancelled.' }; },
    releaseLocal: async r => { w.released.push(r.number); return { state: 'released' }; },
    releaseSlots: async () => true,
    processes: async () => [`${process.pid} ${process.ppid} ${process.pid} 1 ${UID} Mon Nov 11 10:00:00 2026 node test-runner`, ...w.procs.map(p => `${p.pid} ${p.ppid} ${p.pgid} ${p.rss} ${p.uid ?? UID} ${p.start} ${p.args}`)].join('\n'),
    uid: UID,
    cwdOf: async pid => w.procs.find(p => p.pid === pid)?.cwd ?? '/other',
    signal: (target, name) => { w.signals.push([target, name]); const pid = Math.abs(target), at = w.procs.findIndex(p => p.pid === pid); if (at >= 0 && (name === 'SIGKILL' || !w.procs[at].stubborn)) w.procs.splice(at, 1); },
    sleep: async () => {},
  };
  w.move = (state = w.state) => moveToCore({ state, stateFile: '/state/a.json', repoEngine: null }, w.ports);
  return w;
}

test('M1 the first tick moves a full-engine machine: claims, runs, pane, one note per open PR, workers, one line; the second tick writes nothing', async () => {
  const w = fullWorld();
  const result = await w.move();
  assert.equal(result.done, true, result.message);
  // The coordinator pane closes after Herdr shows that it is this repository's coordinator.
  assert.deepEqual(w.herdrCalls.filter(c => !c.startsWith('agent get')), ['pane close pane-1', 'pane get pane-1']);
  assert.equal(w.panes.size, 0);
  // Both live runs of this machine are cancelled and their local allocations released; the other machine's run is not.
  assert.deepEqual(w.cancelled, [11, 12]); assert.deepEqual(w.released, [11, 12]);
  // Both claims of this machine go: the claim comment and pdd:working. A person's labels stay.
  for (const n of [11, 12]) { const issue = w.g.issues.get(n); assert.equal(issue.comments.length, 0); assert.ok(!issue.labels.includes('pdd:working')); }
  assert.deepEqual(w.g.issues.get(12).labels, ['pdd:needs-decision', 'pdd:stuck', 'area:docs']);
  // Machine B keeps its claim and its PR.
  assert.deepEqual(w.g.issues.get(13).labels, ['pdd:working']); assert.equal(w.g.issues.get(13).comments[0].id, w.claimC);
  assert.equal(w.g.pulls.get(31).comments.length, 0);
  // One note on each open PR of this machine's old runs; none on the closed PR.
  for (const n of [21, 22]) { assert.equal(w.g.pulls.get(n).comments.length, 1); assert.match(w.g.pulls.get(n).comments[0].body, new RegExp(RETIRED_NOTE.replace(/[.;]/g, '.'))); }
  assert.equal(w.g.pulls.get(23).comments.length, 0);
  // The old workers of this repository stop: TERM to each process group, KILL for the one that stays. Others stay.
  assert.deepEqual(w.procs.map(p => p.pid), [601, 602, 603]);
  assert.deepEqual(w.signals, [[501, 'SIGTERM'], [502, 'SIGTERM'], [503, 'SIGTERM'], [502, 'SIGKILL']]);
  assert.equal(result.message, `Autopilot moved this machine to the core engine for ${REPO}: closed 1 coordinator chat(s), cancelled 2 old run(s), released 2 claim(s), left 2 PR note(s), stopped 3 old worker process(es) (101 MB).`);
  assert.ok(Number.isFinite(result.journal.done));
  // The saved state: engine core, the journal, no full-engine key; the coordinator's launch profile stays.
  const next = movedState(w.state, result.journal);
  assert.equal(next.engine, 'core'); assert.equal(next.paneId, undefined); assert.equal(next.githubIntake, undefined); assert.equal(next.parking, undefined); assert.equal(next.recipeDelivered, undefined);
  assert.deepEqual(next.launchProfile, { agent: { id: 'codex', kind: 'codex' } }); assert.equal(next.coordinatorId, ME.coordinatorId);
  // The second tick: the move is done, so nothing is read or written.
  const writes = w.g.writes.length, herdr = w.herdrCalls.length;
  const again = await w.move(next);
  assert.equal(again.done, true); assert.equal(again.message, '');
  assert.equal(w.g.writes.length, writes); assert.equal(w.herdrCalls.length, herdr); assert.deepEqual(w.cancelled, [11, 12]);
});

test('M1a each move-journal save finishes before the next step or return; a rejected save is a deferred move', async () => {
  const w = fullWorld();
  let active = 0, maxActive = 0, disk = null;
  w.ports.save = async journal => {
    active++; maxActive = Math.max(maxActive, active);
    await new Promise(resolve => setTimeout(resolve, 5));
    disk = structuredClone(journal);
    active--;
  };
  const moved = await w.move();
  // moveTick adds this line after moveToCore returns. A delayed prior save must not erase it.
  disk = { ...moved.journal, line: moved.message };
  assert.equal(moved.done, true, moved.message);
  assert.equal(maxActive, 1, 'one save finishes before the next starts');
  assert.equal(active, 0, 'the move leaves no background save');
  await new Promise(resolve => setTimeout(resolve, 20));
  assert.equal(disk.line, moved.message, 'no earlier journal save overwrites the moved-state line');

  const failed = fullWorld();
  let saves = 0;
  failed.ports.save = async () => { saves++; throw Error('Timed out waiting for automatic admission; retry.'); };
  const deferred = await failed.move();
  assert.equal(deferred.done, false);
  assert.equal(saves, 1);
  assert.match(deferred.message, /could not save the move journal \(save: Timed out waiting for automatic admission; retry\.\); the next tick retries/);
  assert.equal(deferred.journal.steps.pane, failed.now, 'the caller receives the unsaved checkpoint for diagnostics');
});

test('M1b a run claim is saved before cancellation, and retry keeps cumulative cancellation evidence', async () => {
  const prepare = count => {
    const w = fullWorld(), old = { coordinatorId: 'old-coordinator', machine: ME.machine };
    w.state = { ...w.state, engine: 'core', coordinatorId: 'new-coordinator', paneId: undefined, githubIntake: undefined };
    w.runs = [];
    for (let i = 0; i < count; i++) {
      const issue = 40 + i, claimed = w.g.claim(issue, old);
      const row = run(issue, old);
      row.automaticOrigin.claim = { commentId: String(claimed.comments[0].id), labelEventId: String(claimed.timeline[0].id) };
      w.runs.push(row);
    }
    return w;
  };

  const saved = prepare(1);
  let state = saved.state, failClaimSave = true, claimSaves = 0;
  saved.ports.save = async journal => {
    if (journal.claims?.length) claimSaves++;
    if (journal.claims?.length && failClaimSave) { failClaimSave = false; throw Error('admission busy'); }
    saved.saves.push(structuredClone(journal));
  };
  const held = await saved.move(state);
  assert.equal(held.done, false);
  assert.equal(saved.runs[0].state, 'running', 'a failed claim save prevents cancellation');
  assert.equal(claimSaves, 1, 'a failed pre-cancel save is not retried in this tick');
  assert.match(held.message, /could not save the move journal \(save: admission busy\)/);
  state = { ...state, retiredFull: saved.saves.at(-1) ?? {} };
  assert.equal((await saved.move(state)).done, true);
  assert.equal(saved.g.issues.get(40).comments.length, 0);
  assert.ok(!saved.g.issues.get(40).labels.includes('pdd:working'));

  const partial = prepare(2);
  state = partial.state;
  let failedSecond = false;
  partial.ports.releaseLocal = async row => row.number === 40 ? { state: 'recovery_required' } : { state: 'released' };
  partial.ports.cancelRun = async row => {
    if (row.number === 41 && !failedSecond) { failedSecond = true; throw Error('stop failed'); }
    row.state = 'cancelled'; return { exitCode: 0 };
  };
  const first = await partial.move(state);
  assert.equal(first.done, false);
  assert.equal(partial.runs[0].state, 'cancelled');
  assert.ok(first.journal.claims.some(claim => claim.issue === 40), 'the first cancellation has a durable claim record');
  assert.equal(first.journal.counts.runs, 1);
  assert.deepEqual(first.journal.warnings, ['run #40: the local issue allocation stays']);
  state = { ...state, retiredFull: partial.saves.at(-1) };
  const complete = await partial.move(state);
  assert.equal(complete.done, true);
  assert.equal(complete.journal.counts.runs, 2, 'the retry adds to the first tick count');
  assert.deepEqual(complete.journal.warnings, ['run #40: the local issue allocation stays'], 'the first warning stays once');
  assert.match(complete.message, /cancelled 2 old run\(s\)/);
  for (const issue of [40, 41]) {
    assert.equal(partial.g.issues.get(issue).comments.length, 0, `#${issue} claim comment is released`);
    assert.ok(!partial.g.issues.get(issue).labels.includes('pdd:working'), `#${issue} claim label is released`);
  }
});

test('M1c a failed post-cancel checkpoint reconciles only the saved intent whose run is cancelled', async () => {
  const w = fullWorld(), old = { coordinatorId: 'old-coordinator', machine: ME.machine };
  w.state = { ...w.state, engine: 'core', coordinatorId: 'new-coordinator', paneId: undefined, githubIntake: undefined };
  const claimed = w.g.claim(40, old), row = run(40, old);
  row.automaticOrigin.claim = { commentId: String(claimed.comments[0].id), labelEventId: String(claimed.timeline[0].id) };
  w.runs = [row];
  let failCheckpoint = true, releases = 0;
  w.ports.releaseLocal = async () => { releases++; return { state: 'recovery_required' }; };
  w.ports.save = async journal => {
    if (journal.cancelledRuns?.includes('run-40') && failCheckpoint) { failCheckpoint = false; throw Error('admission busy'); }
    w.saves.push(structuredClone(journal));
  };
  const delayed = await w.move();
  assert.equal(delayed.done, false);
  assert.equal(row.state, 'cancelled', 'the cancellation completed before its checkpoint failed');
  assert.equal(w.cancelled.filter(number => number === 40).length, 1);
  const saved = w.saves.at(-1);
  assert.deepEqual(saved.runIntents, [{ runId: 'run-40', issue: 40 }]);
  assert.equal(saved.counts.runs, 0, 'the failed checkpoint did not claim an unsaved count');
  const complete = await w.move({ ...w.state, retiredFull: saved });
  assert.equal(complete.done, true);
  assert.equal(complete.journal.counts.runs, 1);
  assert.deepEqual(complete.journal.warnings, ['run #40: the local issue allocation stays']);
  assert.equal(w.cancelled.filter(number => number === 40).length, 1, 'a cancelled run is reconciled, not cancelled again');
  assert.equal(releases, 2, 'the local release is retried for the cancelled intent');
});

test('M2 a PR note is never written twice, also when a step runs again', async () => {
  const w = fullWorld();
  await w.move();
  const notes = [21, 22].map(n => w.g.pulls.get(n).comments.length);
  const repeat = { ...w.state, retiredFull: { ...w.saves.at(-1), steps: { pane: 1, runs: 1, claims: 1 }, done: undefined } };
  delete repeat.retiredFull.done;
  assert.equal((await w.move(repeat)).done, true);
  assert.deepEqual([21, 22].map(n => w.g.pulls.get(n).comments.length), notes);
});

test('M3 a run in a merge holds the move for up to 6 ticks, then the move goes on with the reason in its line', async () => {
  const w = fullWorld();
  w.g.pulls.get(22).merged = true; w.g.pulls.get(22).state = 'closed';
  let state = w.state;
  for (let tick = 1; tick <= MAX_DEFERS; tick++) {
    const result = await w.move(state);
    assert.equal(result.done, false);
    assert.match(result.message, new RegExp(`run #12 \\(PR #22 is merged, the run is not done\\) \\(tick ${tick} of ${MAX_DEFERS}\\)`));
    state = { ...state, retiredFull: w.saves.at(-1) };
  }
  assert.deepEqual(w.cancelled, []); assert.equal(w.g.writes.length, 0); assert.equal(w.panes.size, 1);
  const result = await w.move(state);
  assert.equal(result.done, true);
  assert.match(result.message, /it waited 6 tick\(s\) for run #12 \(PR #22 is merged, the run is not done\)\.$/);
});

test('M4 a busy coordinator chat holds the move; an idle one does not', async () => {
  const w = fullWorld();
  w.panes.get('pane-1').agent_status = 'working';
  const held = await w.move();
  assert.equal(held.done, false); assert.match(held.message, /the old coordinator chat \(it is working\)/);
  w.panes.get('pane-1').agent_status = 'idle';
  assert.equal((await w.move({ ...w.state, retiredFull: w.saves.at(-1) })).done, true);
});

test('M5 a failure at a step (GitHub 502, a Herdr error) goes on at the next tick from that step and never repeats a done step', async () => {
  const w = fullWorld();
  w.g.fail = (method, endpoint) => method === 'DELETE' && endpoint.includes('/issues/comments/');
  const first = await w.move();
  assert.equal(first.done, false); assert.match(first.message, /claims: GitHub DELETE .* returned 502.*the next tick goes on from this step/);
  assert.deepEqual(Object.keys(w.saves.at(-1).steps), ['pane', 'runs']);
  w.g.fail = null;
  const ports = w.ports;
  w.ports = { ...ports, herdr: async () => { throw Object.assign(Error('down'), { code: 'internal' }); } };
  const second = await w.move({ ...w.state, retiredFull: w.saves.at(-1) });
  assert.equal(second.done, true, second.message);
  assert.deepEqual(w.cancelled, [11, 12], 'the runs step did not run again');
  assert.equal(w.g.issues.get(11).comments.length, 0);
  // A Herdr error at the pane step keeps the move at that step.
  const v = fullWorld();
  v.ports.herdr = async () => { throw Object.assign(Error('down'), { code: 'internal' }); };
  const held = await v.move();
  assert.equal(held.done, false); assert.match(held.message, /pane: Herdr could not read the old coordinator pane \(internal\)/);
  assert.deepEqual(v.cancelled, []);
});

test('M6 a pane that Herdr shows for another folder or agent is not closed; a missing Herdr has nothing to close', async () => {
  const w = fullWorld();
  w.panes.get('pane-1').cwd = '/elsewhere';
  const result = await w.move();
  assert.equal(result.done, true); assert.equal(w.panes.size, 1); assert.equal(result.journal.counts.keptPanes, 1);
  const v = fullWorld();
  v.ports.herdr = async () => { throw Object.assign(Error('Herdr is not installed'), { code: 'herdr_missing' }); };
  assert.equal((await v.move()).done, true);
});

test('M7 a machine that already ran the core engine: no claim search and no PR read; its old workers stop with one line; with nothing found, no line', async () => {
  const w = fullWorld();
  w.runs = []; w.state = { ...w.state, engine: 'core', paneId: undefined, githubIntake: undefined };
  const result = await w.move();
  assert.equal(result.done, true); assert.match(result.message, /released 0 claim\(s\), left 0 PR note\(s\), stopped 1 old worker process\(es\) \(1 MB\)\.$/);
  assert.deepEqual(w.g.writes, []); assert.equal(w.g.issues.get(11).comments.length, 1, 'the core never loses a claim');
  assert.deepEqual(w.procs.map(p => p.pid), [501, 502, 601, 602, 603]);
  const busy = fullWorld();
  busy.runs = []; busy.state = { ...busy.state, engine: 'core', paneId: undefined };
  busy.procs = [{ pid: 700, ppid: 1, pgid: 700, rss: 1, start: 'Mon Nov 11 10:00:07 2026', args: 'node unrelated', cwd: '/other' }];
  assert.equal((await busy.move()).message, '', 'nothing found and the engine was core: no line');
  const empty = fullWorld();
  empty.runs = []; empty.state = { ...empty.state, engine: 'core', paneId: undefined };
  empty.procs = [];
  const idle = await empty.move();
  assert.equal(idle.done, true, idle.message);
  assert.equal(idle.message, '', 'an empty complete process inventory is a valid no-op');
  assert.deepEqual(empty.signals, []);
  const unavailable = fullWorld();
  unavailable.runs = []; unavailable.state = { ...unavailable.state, engine: 'core', paneId: undefined };
  unavailable.ports.processes = async () => '';
  const held = await unavailable.move();
  assert.equal(held.done, false);
  assert.equal(held.journal.steps.workers, undefined);
  assert.deepEqual(unavailable.signals, []);
  const changed = fullWorld();
  changed.runs = [run(9, ME, { state: 'cancelled', runDir: '/repo/.git/pdd/runs/9-cancelled-abcd1234' })];
  changed.state = { ...changed.state, engine: 'core', paneId: undefined };
  changed.procs = [{ pid: 701, ppid: 1, pgid: 701, rss: 1, start: 'Mon Nov 11 10:00:07 2026', args: `node /pkg/src/workflow-worker-completion.mjs ${JSON.stringify({ runId: 'r0', runDir: '/repo/.git/pdd/runs/9-cancelled-abcd1234', sourceRoot: '/repo' })}` }];
  const completeInventory = changed.ports.processes;
  let inventories = 0;
  changed.ports.processes = async () => ++inventories === 1 ? completeInventory() : '';
  const retried = await changed.move();
  assert.equal(retried.done, false);
  assert.equal(retried.journal.steps.workers, undefined);
  assert.deepEqual(changed.signals, [], 'an unreadable recheck never treats a saved worker as gone');
});

test('retirement leaves a current-user manual helper in a cancelled worktree, and does not inspect another user', async () => {
  const w = fullWorld(), cwdReads = [];
  for (const item of w.runs) item.state = 'cancelled';
  w.procs = [
    { pid: 800, ppid: 1, pgid: 800, rss: 1, uid: 502, start: 'Mon Nov 11 10:01:00 2026', args: 'node unrelated', cwd: '/repo.pdd-worktrees/11' },
    { pid: 801, ppid: 1, pgid: 801, rss: 1, uid: UID, start: 'Mon Nov 11 10:01:01 2026', args: 'node helper', cwd: '/repo.pdd-worktrees/11' },
    { pid: 802, ppid: 1, pgid: 802, rss: 1, uid: UID, start: 'Mon Nov 11 10:01:02 2026', args: 'node helper', cwd: '/repo.pdd-worktrees/active' }
  ];
  w.ports.cwdOf = async pid => { cwdReads.push(pid); return w.procs.find(row => row.pid === pid)?.cwd ?? null; };
  const journal = { wasFull: false, steps: { pane: 1, runs: 1, claims: 1, notes: 1, slots: 1 }, counts: {}, defers: 0 };
  const result = await w.move({ ...w.state, retiredFull: journal });
  assert.equal(result.done, false); assert.match(result.message, /ownership is ambiguous/);
  assert.deepEqual(w.procs.map(row => row.pid), [800, 801, 802]); assert.deepEqual(w.signals, []); assert.deepEqual(cwdReads, [801]);
  const completed = fullWorld();
  for (const item of completed.runs) item.state = 'completed';
  completed.procs = [{ pid: 804, ppid: 1, pgid: 804, rss: 1, uid: UID, start: 'Mon Nov 11 10:01:04 2026', args: 'node helper', cwd: '/repo.pdd-worktrees/11' }];
  const held = await completed.move({ ...completed.state, retiredFull: journal });
  assert.equal(held.done, false); assert.match(held.message, /ownership is ambiguous/, 'a recorded completed run root is still protected');
});

test('retirement accepts a parentless process that exits before cwd evidence, but retains one whose cwd is unreadable', async () => {
  const setup = () => {
    const w = fullWorld();
    for (const item of w.runs) item.state = 'cancelled';
    w.procs = [{ pid: 801, ppid: 1, pgid: 801, rss: 1, uid: UID, start: 'Mon Nov 11 10:01:01 2026', args: 'node helper' }];
    return w;
  };
  const gone = setup();
  gone.ports.cwdOf = async pid => { gone.procs = gone.procs.filter(row => row.pid !== pid); return null; };
  const journal = { wasFull: false, steps: { pane: 1, runs: 1, claims: 1, notes: 1, slots: 1 }, counts: {}, defers: 0 };
  assert.equal((await gone.move({ ...gone.state, retiredFull: journal })).done, true);
  const unreadable = setup();
  unreadable.ports.cwdOf = async () => { unreadable.procs[0].args = 'node changed-command'; return null; };
  const held = await unreadable.move({ ...unreadable.state, retiredFull: journal });
  assert.equal(held.done, false); assert.match(held.message, /working-directory evidence is unreadable/); assert.deepEqual(unreadable.signals, []);
});

test('M8 the engine before 0.1.29: the saved engine, else pdd.json, else full; the core keeps its own claims (hashed machine id)', () => {
  assert.equal(engineBefore({ engine: 'core' }, 'full'), 'core');
  assert.equal(engineBefore({ engine: 'full' }, 'core'), 'full');
  assert.equal(engineBefore({}, 'core'), 'core');
  assert.equal(engineBefore({}, null), 'full');
  assert.equal(claimRecord(claimBody(ME, 7)).labelEventId, '7');
  assert.equal(claimRecord('plain words'), null);
  assert.equal(oldProcessOf(`node /x/workflow-worker-completion.mjs {"runDir":"/repo/.git/pdd/runs/4"}`, { runsRoot: '/repo/.git/pdd/runs', stateFile: '/s.json' }), 'worker');
  assert.equal(oldProcessOf(`node /x/workflow-worker-completion.mjs {"runDir":"/repo/.git/pdd/runs-old/4"}`, { runsRoot: '/repo/.git/pdd/runs', stateFile: '/s.json' }), null);
  assert.equal(oldProcessOf(`node /x/workflow-worker-completion.mjs /tmp/identity.json`, { runsRoot: '/repo/.git/pdd/runs', stateFile: '/s.json' }), null);
  assert.equal(oldProcessOf(`node /x/autopilot-launcher.mjs --coordinator-idle {"stateFile":"/s.json"}`, { runsRoot: '/r', stateFile: '/s.json' }), 'coordinator-idle');
  assert.equal(oldProcessOf(`node /x/autopilot-launcher.mjs --start-scan-wait {"stateFile":"/s.json"}`, { runsRoot: '/r', stateFile: '/s.json' }), null);
  assert.equal(oldProcessOf('node agent /repo.pdd-worktrees/run-7/task.mjs', { runsRoot: '/r', stateFile: '/s.json', runRoots: ['/repo.pdd-worktrees/run-7'] }), null);
  assert.equal(oldProcessOf('node agent /repo.pdd-worktrees/run-8/task.mjs', { runsRoot: '/r', stateFile: '/s.json', runRoots: ['/repo.pdd-worktrees/run-7'] }), null);
  assert.equal(parseProcesses('  12   1  12  300 node a b\nbad row\n'), null, 'a partial inventory is not cleanup evidence');
  // Linux without ps: /proc gives the same rows; a kernel thread (empty cmdline) and a process that ended are skipped.
  const proc = { '/proc/7/cmdline': 'node\0/x/workflow-worker-completion.mjs\0{"runDir":"/r/7"}\0', '/proc/7/stat': '7 (node (w)) S 1 7 7 0 -1 0 0 0 0 0 1 2 0 0 20 0 1 0 100 9000 25 0', '/proc/7/status': 'Name:\tnode\nUid:\t501\t501\t501\t501\n' };
  const fs = { readdirSync: () => ['7', '9', 'self'], readFileSync: path => { if (!(path in proc)) throw Object.assign(Error('gone'), { code: 'ENOENT' }); return proc[path]; } };
  assert.deepEqual(parseProcesses(procTable(fs)), [{ pid: 7, ppid: 1, pgid: 7, rss: 100, uid: 501, start: '@100', args: 'node /x/workflow-worker-completion.mjs {"runDir":"/r/7"}' }]);
  const live = { readdirSync: () => ['7'], readFileSync: path => path.endsWith('/status') ? (() => { throw Object.assign(Error('denied'), { code: 'EACCES' }); })() : proc[path] };
  assert.throws(() => procTable(live), /denied/, 'an unreadable live process makes the inventory unavailable');
  const noUid = { readdirSync: () => ['7'], readFileSync: path => path.endsWith('/status') ? 'Name:\tnode\n' : proc[path] };
  assert.throws(() => procTable(noUid), /stable identity/, 'a live row without uid is not omitted');
  assert.match(FULL_ENGINE_REMOVED, /full Autopilot engine is removed/);
});

// Real processes: a cancelled run's completion workers (one ignores SIGTERM, one has a waiting child) are all gone
// after the move, and a worker of another repository stays.
test('M9 no old worker is left after the move (real processes)', { skip: process.platform === 'win32' }, async t => {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-retire-')));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  mkdirSync(join(dir, 'bin'));
  writeFileSync(join(dir, 'bin', 'workflow-worker-completion.mjs'), `import { spawn } from 'node:child_process';
if (process.env.STUBBORN) process.on('SIGTERM', () => {});
if (process.env.CHILD) spawn(process.execPath, ['-e', 'setInterval(() => {}, 1000)'], { stdio: 'ignore' });
setInterval(() => {}, 1000);\n`);
  const runsRoot = join(dir, 'repo', '.git', 'pdd', 'runs');
  const start = (runDir, env = {}) => { const child = spawn(process.execPath, [join(dir, 'bin', 'workflow-worker-completion.mjs'), JSON.stringify({ runId: 'r', runDir })], { detached: true, stdio: 'ignore', env: { ...process.env, ...env } }); child.unref(); return child.pid; };
  const mine = [start(join(runsRoot, '7')), start(join(runsRoot, '8'), { STUBBORN: '1' }), start(join(runsRoot, '9'), { CHILD: '1' })];
  const other = start(join(dir, 'other', '.git', 'pdd', 'runs', '7'));
  t.after(() => { for (const pid of [...mine, other]) { try { process.kill(-pid, 'SIGKILL'); } catch { /* gone */ } } });
  const ps = () => spawnSync('ps', ['-A', '-ww', '-o', 'pid=', '-o', 'ppid=', '-o', 'pgid=', '-o', 'rss=', '-o', 'lstart=', '-o', 'args='], { encoding: 'utf8' }).stdout;
  const alive = pid => { try { process.kill(pid, 0); return true; } catch { return false; } };
  for (let i = 0; i < 100 && !parseProcesses(ps()).some(p => p.pgid === mine[2] && p.pid !== mine[2]); i++) await new Promise(r => setTimeout(r, 50));
  const child = parseProcesses(ps()).find(p => p.pgid === mine[2] && p.pid !== mine[2])?.pid;
  assert.ok(child, 'the waiting child runs');
  const journal = { wasFull: false, steps: { pane: 1, runs: 1, claims: 1, notes: 1, slots: 1 }, counts: {}, defers: 0 };
  const signals = [];
  const result = await moveToCore({ state: { repo: REPO, cwd: join(dir, 'repo'), ...ME, retiredFull: journal }, stateFile: join(dir, 's.json') }, {
    commonDir: join(dir, 'repo', '.git'), save: () => {}, gh: async () => assert.fail('no GitHub call'), processes: async () => ps(),
    listRuns: async () => mine.map((pid, index) => ({ repo: REPO, state: 'cancelled', root: join(dir, 'repo.pdd-worktrees', String(index + 7)), runDir: join(runsRoot, String(index + 7)), automaticOrigin: { machine: ME.machine } })),
    cwdOf: async () => join(dir, 'other'),
    signal: (pid, name) => { signals.push([pid, name]); try { process.kill(pid, name); } catch { /* gone */ } }, sleep: ms => new Promise(r => setTimeout(r, ms)),
  });
  assert.equal(result.done, true);
  assert.equal(result.journal.counts.workers, 4); assert.equal(result.journal.counts.killed, 1);
  assert.ok(signals.some(([pid, name]) => pid === child && name === 'SIGTERM'), 'the captured descendant is stopped by PID');
  for (let i = 0; i < 40 && [...mine, child].some(alive); i++) await new Promise(r => setTimeout(r, 50));
  assert.deepEqual([...mine, child].filter(alive), [], 'no worker of this repository is left');
  assert.ok(alive(other), 'the other repository keeps its worker');
});

// The launcher: the move runs inside the tick, never touches the timer, saves engine core, and the core tick follows.
test('M10 a full-engine state moves at its first tick without a timer call; the next tick is a core tick', async t => {
  const { tickAutopilot, runAutopilotLauncher } = await import('../src/autopilot-launcher.mjs');
  const w = await coreWorld(t);
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], testCommand: 'npm test', label: 'pdd:autopilot' } }));
  w.issue(17, { labels: ['pdd:autopilot'] });
  w.issue(5); w.github.claim(5, { coordinatorId: 'coord-a', machine: 'machine-a' });
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel'), stateRoot = join(w.dir, 'state');
  const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);
  mkdirSync(stateRoot, { recursive: true });
  writeFileSync(stateFile, JSON.stringify({ enabled: true, cwd, repo: 'acme/widgets', defaultBranch: 'main', coordinatorId: 'coord-a', machine: 'machine-a', paneId: 'pane-9', workspaceId: 'ws-9',
    agent: { id: 'codex', kind: 'codex', command: 'codex' }, packageRoot: join(w.dir, 'pkg'), parking: {}, recipeDelivered: true, timerMinutes: 30 }));
  const timer = [], notices = [], programs = [];
  const ports = { stateRoot, now: w.now, machineGuard: w.machineGuard, env: { HOME: process.env.HOME, PATH: process.env.PATH }, timer: async action => { timer.push(action); return true; }, warn: () => {}, notice: text => notices.push(text),
    herdr: async args => { programs.push(`herdr ${args.join(' ')}`); throw Object.assign(Error('gone'), { code: 'agent_not_found' }); },
    run: async (command, args, options = {}) => {
      programs.push(command);
      if (command === 'gh') return w.gh(args, options);
      if (command !== 'git') assert.fail(`unexpected program ${command}`);
      const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' }); return { code: r.status, stdout: r.stdout, stderr: r.stderr };
    },
    movePorts: { processes: async () => `${process.pid} ${process.ppid} ${process.pid} 1 501 Mon Nov 11 10:00:00 2026 node test-runner\n700 1 700 1 501 Mon Nov 11 10:00:07 2026 node unrelated`, releaseSlots: async () => false },
    corePorts: { jobs: w.jobs, checkBase: async () => ({ exitCode: 0, message: 'ok' }), agentReady: async () => true } };
  const first = await tickAutopilot(stateFile, ports);
  assert.match(first.message, /Autopilot core: 1 started/, first.message);
  assert.deepEqual(timer, [], 'the tick never stops, starts or reloads its own timer');
  assert.ok(!programs.some(p => /launchctl|systemctl/.test(p)));
  assert.equal(notices.length, 1); assert.match(notices[0], /moved this machine to the core engine for acme\/widgets: closed 0 coordinator chat\(s\), cancelled 0 old run\(s\), released 1 claim\(s\)/);
  assert.ok(!w.github.issues.get(5).labels.includes('pdd:working'), 'this machine\'s old claim is released');
  const saved = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(saved.engine, 'core'); assert.ok(Number.isFinite(saved.retiredFull.done)); assert.equal(saved.paneId, undefined); assert.equal(saved.parking, undefined);
  const status = await runAutopilotLauncher({ command: 'status', cwd, packageRoot: join(w.dir, 'pkg'), env: ports.env }, ports);
  assert.match(status.message, /Moved from the full engine at .*: Autopilot moved this machine/);
  assert.match(status.message, /run pdd autopilot start to use 10 minutes/);
  w.advance(10 * 60 * 1000);
  const second = await tickAutopilot(stateFile, ports);
  assert.match(second.message, /Autopilot core:/); assert.equal(notices.length, 1);
});

test('M11 start: --engine full is refused with one line; a start with no opt-in label asks for one and starts nothing', async t => {
  const { runAutopilotLauncher } = await import('../src/autopilot-launcher.mjs');
  const full = await runAutopilotLauncher({ command: 'start', engine: 'full', cwd: '/nowhere', issues: [] }, {});
  assert.deepEqual(full, { exitCode: 2, message: FULL_ENGINE_REMOVED });
  assert.equal((await runAutopilotLauncher({ command: 'start', engine: 'fast', cwd: '/nowhere', issues: [] }, {})).exitCode, 2);
  const w = await coreWorld(t);
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], testCommand: 'npm test' } }));
  w.issue(17);
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel'), stateRoot = join(w.dir, 'state');
  const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);
  const timer = [], writes = () => w.github.writes?.length ?? 0, before = writes();
  const ports = { stateRoot, now: w.now, machineGuard: w.machineGuard, env: { HOME: process.env.HOME, PATH: process.env.PATH }, timer: async action => { timer.push(action); return true; }, warn: () => {},
    doctorPorts: { run: async () => ({ code: 0, stdout: '', stderr: '' }) },
    run: async (command, args, options = {}) => {
      if (command === 'gh') return w.gh(args, options);
      if (command !== 'git') return { code: 0, stdout: '', stderr: '' };
      const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' }); return { code: r.status, stdout: r.stdout, stderr: r.stderr };
    } };
  // Doctor is not under test here: a passing report.
  const { runAutopilotLauncher: launcher } = await import('../src/autopilot-launcher.mjs');
  const result = await launcher({ command: 'start', cwd, packageRoot: join(w.dir, 'pkg'), env: ports.env, issues: [] }, { ...ports, doctorPorts: { ...ports, selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex' }) } });
  if (result.exitCode !== 1 || !/opt-in label/.test(result.message)) assert.fail(result.message);
  assert.match(result.message, /pdd autopilot start --label pdd:autopilot.*Nothing was started or claimed\.$/);
  assert.deepEqual(timer, []);
  assert.equal(existsSync(stateFile), false, 'no state is saved before the label question');
  assert.equal(writes(), before, 'no GitHub write');
  assert.ok(!w.github.issues.get(17).labels.includes('pdd:working'));
  // With a label, a new state is a core state and its first tick claims only a labeled issue.
  mkdirSync(join(w.dir, 'pkg'), { recursive: true }); writeFileSync(join(w.dir, 'pkg', 'package.json'), JSON.stringify({ version: '0.1.29' }));
  w.issue(18, { labels: ['pdd:autopilot'] });
  const started = await launcher({ command: 'start', label: 'pdd:autopilot', cwd, packageRoot: join(w.dir, 'pkg'), env: ports.env, issues: [] },
    { ...ports, selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex' }), doctorPorts: { ...ports, selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex' }) },
      corePorts: { jobs: w.jobs, checkBase: async () => ({ exitCode: 0, message: 'ok' }), agentReady: async () => true } });
  assert.equal(started.exitCode, 0, started.message);
  assert.match(started.message, /Mode auto · issues with pdd:autopilot · agent codex/);
  assert.doesNotMatch(started.message, /moved this machine/, 'a fresh repository has nothing to move');
  const fresh = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(fresh.engine, 'core'); assert.equal(fresh.label, 'pdd:autopilot'); assert.ok(Number.isFinite(fresh.retiredFull?.done));
  assert.deepEqual(timer, ['start']);
  assert.ok(w.job(18, 'build') && !w.job(17), 'only the labeled issue starts');
});

// launchd: start rewrites the LaunchAgent with the 10-minute interval before the tick; the tick that moves the
// machine (in start, and from the timer) never calls launchctl, so it never unloads its own job.
test('M12 launchd: start writes StartInterval 600 and only start calls launchctl; the moving tick never does', async t => {
  const { runAutopilotLauncher, tickAutopilot } = await import('../src/autopilot-launcher.mjs');
  const w = await coreWorld(t);
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], testCommand: 'npm test', label: 'pdd:autopilot' } }));
  mkdirSync(join(w.dir, 'pkg'), { recursive: true }); writeFileSync(join(w.dir, 'pkg', 'package.json'), JSON.stringify({ version: '0.1.29' }));
  const home = join(w.dir, 'home'); mkdirSync(home, { recursive: true });
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel'), stateRoot = join(w.dir, 'state');
  const id = createHash('sha256').update(cwd).digest('hex').slice(0, 20), stateFile = join(stateRoot, `${id}.json`);
  mkdirSync(stateRoot, { recursive: true });
  // A full-engine state of an older pdd: no engine, a coordinator pane, a 30-minute timer.
  writeFileSync(stateFile, JSON.stringify({ enabled: true, cwd, repo: 'acme/widgets', defaultBranch: 'main', coordinatorId: 'coord-a', machine: 'machine-a', paneId: 'pane-1', workspaceId: 'ws-1',
    agent: { id: 'codex', kind: 'codex', command: 'codex' }, packageRoot: join(w.dir, 'pkg'), timerMinutes: 30, environment: { HOME: home, PATH: process.env.PATH } }));
  const calls = [], phase = { now: 'start' };
  const run = async (command, args, options = {}) => {
    calls.push([phase.now, command, ...args.slice(0, 2)]);
    if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: JSON.stringify({ nameWithOwner: 'acme/widgets', defaultBranchRef: { name: 'main' } }), stderr: '' };
    if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
    if (command === 'gh') return w.gh(args, options);
    if (command === 'launchctl') return { code: args[0] === 'print' ? 1 : 0, stdout: '', stderr: '' };
    if (command !== 'git') return { code: 0, stdout: '', stderr: '' };
    const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' }); return { code: r.status, stdout: r.stdout, stderr: r.stderr };
  };
  const agent = async () => ({ id: 'codex', kind: 'codex', command: 'codex' });
  const ports = { stateRoot, now: w.now, machineGuard: w.machineGuard, env: { HOME: home, PATH: process.env.PATH }, platform: 'darwin', uid: 501, warn: () => {}, notice: () => {}, run, selectAgent: agent,
    doctorPorts: { run: async (command, args, options) => command === 'git' ? run(command, args, options) : { code: 0, stdout: '', stderr: '' }, selectAgent: agent },
    herdr: async () => { phase.herdr = true; throw Object.assign(Error('gone'), { code: 'agent_not_found' }); },
    movePorts: { processes: async () => `${process.pid} ${process.ppid} ${process.pid} 1 501 Mon Nov 11 10:00:00 2026 node test-runner\n700 1 700 1 501 Mon Nov 11 10:00:07 2026 node unrelated`, releaseSlots: async () => false },
    corePorts: { jobs: w.jobs, checkBase: async () => ({ exitCode: 0, message: 'ok' }), agentReady: async () => true } };
  // The tick inside start: every launchctl call must come before it.
  const started = await runAutopilotLauncher({ command: 'start', cwd, packageRoot: join(w.dir, 'pkg'), env: ports.env, issues: [] }, { ...ports, run: async (command, args, options) => {
    if (command === 'gh' && args.includes('--include') && calls.some(([, c]) => c === 'launchctl')) phase.now = 'tick';
    return run(command, args, options);
  } });
  assert.equal(started.exitCode, 0, started.message);
  assert.match(started.message, /Autopilot moved this machine to the core engine for acme\/widgets/);
  const plist = readFileSync(join(home, 'Library', 'LaunchAgents', `pdd-autopilot-${id}.plist`), 'utf8');
  assert.match(plist, /<key>StartInterval<\/key><integer>600<\/integer>/);
  assert.deepEqual(calls.filter(([p, c]) => p === 'tick' && c === 'launchctl'), [], 'the tick in start calls no launchctl');
  assert.equal(JSON.parse(readFileSync(stateFile, 'utf8')).timerMinutes, 10);
  // A timer tick after the move: no launchctl, no Herdr.
  phase.now = 'timer'; phase.herdr = false; w.advance(10 * 60 * 1000);
  await tickAutopilot(stateFile, ports);
  assert.deepEqual(calls.filter(([p, c]) => p === 'timer' && ['launchctl', 'systemctl'].includes(c)), []);
  assert.equal(phase.herdr, false);
});

// The core tick's issue list (queryIssues): a list of two pages is read in full, then only the issues changed since
// that read, until 6 hours pass. A closed issue leaves the cached list.
test('M13 the core tick reads only changed issues between full reads of a two-page list', async t => {
  const { tickAutopilot } = await import('../src/autopilot-launcher.mjs');
  const w = await coreWorld(t);
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], testCommand: 'npm test', label: 'pdd:autopilot' } }));
  for (let n = 1; n <= 120; n++) w.issue(n);
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel'), stateRoot = join(w.dir, 'state');
  const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);
  mkdirSync(stateRoot, { recursive: true });
  writeFileSync(stateFile, JSON.stringify({ enabled: true, cwd, repo: 'acme/widgets', defaultBranch: 'main', coordinatorId: 'coord-a', machine: 'machine-a', engine: 'core',
    label: 'pdd:autopilot', retiredFull: { done: 1 }, agent: { id: 'codex', kind: 'codex', command: 'codex' }, packageRoot: join(w.dir, 'pkg') }));
  const lists = [];
  const ports = { stateRoot, now: w.now, machineGuard: w.machineGuard, env: { HOME: process.env.HOME, PATH: process.env.PATH }, timer: async () => true, warn: () => {},
    run: async (command, args, options = {}) => {
      if (command === 'gh') { const endpoint = args.find(arg => /^repos\/acme\/widgets\/issues\?/.test(String(arg))); if (endpoint) lists.push(endpoint); return w.gh(args, options); }
      if (command !== 'git') assert.fail(`unexpected program ${command}`);
      const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' }); return { code: r.status, stdout: r.stdout, stderr: r.stderr };
    },
    corePorts: { jobs: w.jobs, checkBase: async () => ({ exitCode: 0, message: 'ok' }), agentReady: async () => true } };
  await tickAutopilot(stateFile, ports);
  assert.ok(lists.some(e => e.includes('state=open')) && lists.some(e => e.includes('page=2')), 'the first tick reads the full two-page list');
  assert.equal(JSON.parse(readFileSync(stateFile, 'utf8')).cachedIssues.length, 120);
  lists.length = 0; w.advance(10 * 60 * 1000);
  w.github.close(7); w.issue(121);
  await tickAutopilot(stateFile, ports);
  assert.ok(lists.length && lists.every(e => e.includes('state=all') && e.includes('&since=')), `between full reads only changed issues are read: ${lists.join(' ')}`);
  const cached = JSON.parse(readFileSync(stateFile, 'utf8')).cachedIssues.map(row => row.number);
  assert.ok(!cached.includes(7) && cached.includes(121), 'the closed issue left the list; the new one came in');
  lists.length = 0; w.advance(6 * 60 * 60 * 1000);
  await tickAutopilot(stateFile, ports);
  assert.ok(lists.some(e => e.includes('state=open')), 'after 6 hours the whole open list is read again');
});
