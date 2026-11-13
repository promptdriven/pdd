import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { coreWorld } from './helpers/core-world.mjs';

const MIN = 60 * 1000;
const jobFile = (w, n) => { try { return JSON.parse(readFileSync(join(w.root, 'jobs', `${n}.json`), 'utf8')); } catch { return null; } };
const isLaneList = args => args.some(x => String(x).includes('labels=pdd%3Amerge-lane'));
const isLanePost = (args, options) => args.includes('POST') && String(options?.input ?? '').includes('pdd:merge-lane');
const okList = rows => ({ code: 0, stdout: `HTTP/2.0 200 OK\r\nX-Ratelimit-Remaining: 4000\r\n\r\n${JSON.stringify(rows)}`, stderr: '' });

test('ML1: lane entry and race guard read GET issues/N when the label search list lags right after POST', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  await w.tick();
  const { pr } = w.build(17);
  await w.tick();
  w.review(17, 'PASS');
  w.suite(17, 0);

  let ownReads = 0;
  const baseGh = w.ports().gh;
  await w.tick({
    gh: async (args, options) => {
      if (isLaneList(args)) return okList([]);
      if (args.includes('GET') && args.some(x => x === `repos/${w.state.repo}/issues/${pr.number}`)) ownReads++;
      return baseGh(args, options);
    },
  });

  assert.deepEqual(w.github.merges, [pr.number], 'merges in the same tick even when issues?labels=pdd:merge-lane lags empty');
  assert.ok(ownReads >= 1, 'read GET repos/.../issues/N for consistent PR labels');

  // Race tie-break still holds when the list lags on our PR but shows a lower-numbered winner (#100 < #101).
  const v = await coreWorld(t, { settings: { runs: 2 } });
  v.issue(17);
  v.issue(18);
  await v.tick();
  const a = v.build(17), b = v.build(18);
  await v.tick();
  v.review(18, 'PASS');
  v.suite(18, 0);
  v.baseCommit('person.txt', 'main moved\n');
  const vGh = v.ports().gh;
  await v.tick({
    gh: async (args, options) => {
      const r = await vGh(args, options);
      if (isLanePost(args, options) && args.some(x => String(x).includes(`/issues/${b.pr.number}/labels`))) a.pr.labels.push('pdd:merge-lane');
      if (isLaneList(args) && a.pr.labels.includes('pdd:merge-lane')) {
        return okList([{ number: a.pr.number, state: 'open', labels: [{ name: 'pdd:merge-lane' }], pull_request: {} }]);
      }
      return r;
    },
  });
  assert.equal(jobFile(v, 18)?.lane?.state, 'waiting');
  assert.equal(jobFile(v, 18)?.lane?.holder, a.pr.number);
  assert.ok(!b.pr.labels.includes('pdd:merge-lane'), 'losing higher PR drops its own label even when absent from list');
});

test('ML2: when a holder frees the lane (merge, END or conflict exit), the next waiting green PR enters the lane in the same tick', async t => {
  // Case A: Holder #18 (higher issue number, claimed first) merges; waiting #17 (17 < 18, already visited in readJobs) enters final & refreshes in the same tick.
  const w = await coreWorld(t, { settings: { runs: 2 } });
  w.github.mergeMovesBase = true;
  w.issue(18);
  await w.tick();
  w.advance(MIN);
  w.issue(17);
  await w.tick();

  const b = w.build(18);
  const a = w.build(17);
  await w.tick();
  w.review(18, 'PASS'); w.suite(18, 0);
  w.baseCommit('seed.txt', 'move base once\n');
  await w.tick(); // #18 enters final and refreshes
  assert.equal(jobFile(w, 18)?.lane?.state, 'final');

  // Now #17 becomes green while #18 holds the lane; on the next tick #17 waits first (17 < 18), then #18 merges!
  w.review(17, 'PASS'); w.suite(17, 0);
  await w.tick(); // starts suite for #18's refreshed head; #17 enters waiting
  assert.equal(jobFile(w, 17)?.lane?.state, 'waiting');
  const head17Before = jobFile(w, 17).head;
  w.github.setChecks(jobFile(w, 18).head);
  w.suite(18, 0);

  await w.tick(); // #17 runs first (still waiting), then #18 merges -> #17 MUST enter final & refresh in this same tick!
  assert.deepEqual(w.github.merges, [b.pr.number]);
  const job17 = jobFile(w, 17);
  assert.equal(job17?.lane?.state, 'final', '#17 enters final in the same tick that #18 merged');
  assert.ok(a.pr.labels.includes('pdd:merge-lane'), '#17 holds pdd:merge-lane in the same tick');
  assert.notEqual(job17.head, head17Before, '#17 already refreshed onto the new main in the same tick');

  // Case B: Holder #18 exits the lane on an END (closed PR) while #17 (17 < 18) is waiting -> #17 takes the lane and merges in the same tick!
  const v = await coreWorld(t, { settings: { runs: 2 } });
  v.issue(18);
  await v.tick();
  v.advance(MIN);
  v.issue(17);
  await v.tick();
  const vb = v.build(18), va = v.build(17);
  await v.tick();
  v.review(18, 'PASS'); v.suite(18, 0);
  v.review(17, 'PASS'); v.suite(17, 0);
  v.baseCommit('hold.txt', 'keep #18 in final\n');
  await v.tick(); // #18 enters final & refreshes; #17 waits
  assert.equal(jobFile(v, 18)?.lane?.state, 'final');
  await v.tick(); // #17 is in waiting
  assert.equal(jobFile(v, 17)?.lane?.state, 'waiting');

  // #18's PR is closed without merge (triggers END + leaveLane); #17 refreshes in the same tick!
  vb.pr.state = 'closed';
  const vHead17 = jobFile(v, 17).head;
  await v.tick();
  assert.equal(jobFile(v, 18), null, '#18 ended');
  assert.equal(jobFile(v, 17)?.lane?.state, 'final', '#17 took the freed lane in the same tick');
  assert.notEqual(jobFile(v, 17)?.head, vHead17, '#17 refreshed in the same tick');
  await v.tick();
  v.github.setChecks(jobFile(v, 17).head);
  v.suite(17, 0);
  await v.tick();
  assert.deepEqual(v.github.merges, [va.pr.number]);
});

test('ML3: core factory simulation merges 4 queued green PRs under GitHub label-list lag well within the 40-merges/day budget', async t => {
  const issues = [20, 19, 18, 17]; // Claimed highest-issue-first so every merge tests out-of-order same-tick handoff
  const w = await coreWorld(t, { settings: { runs: 4 } });
  w.github.mergeMovesBase = true;

  for (const n of issues) {
    w.issue(n);
    await w.tick();
    w.advance(MIN);
  }
  const prs = new Map();
  for (const n of issues) {
    const { pr } = w.build(n);
    prs.set(n, pr);
  }
  await w.tick();
  for (const n of issues) {
    w.review(n, 'PASS');
    w.suite(n, 0);
  }

  // Simulate GitHub's label-list lag: after any POST /issues/N/labels, that PR is invisible in issues?labels=pdd:merge-lane during that tick.
  let ticks = 0;
  const startAt = w.now();
  while (w.github.merges.length < issues.length && ticks < 25) {
    ticks++;
    const freshlyLabeled = new Set();
    const baseGh = w.ports().gh;
    await w.tick({
      gh: async (args, options) => {
        if (isLanePost(args, options)) {
          const m = /\/issues\/(\d+)\/labels$/.exec(args.find(x => String(x).startsWith('repos/')) ?? '');
          if (m) freshlyLabeled.add(Number(m[1]));
        }
        const r = await baseGh(args, options);
        if (isLaneList(args)) {
          const rows = [...w.github.prs.values()]
            .filter(pr => pr.state === 'open' && pr.labels.includes('pdd:merge-lane') && !freshlyLabeled.has(pr.number))
            .map(pr => ({ number: pr.number, state: 'open', labels: pr.labels.map(name => ({ name })), pull_request: {} }));
          return okList(rows);
        }
        return r;
      },
    });
    // Between 10-minute ticks, any running CI + local suite on a refreshed head completes.
    for (const n of issues) {
      const job = jobFile(w, n);
      if (!job) continue;
      w.github.setChecks(job.head);
      if (w.job(n, 'suite') && w.alive.has(w.job(n, 'suite').pid)) w.suite(n, 0);
    }
    if (w.github.merges.length < issues.length) w.advance(10 * MIN);
  }

  const elapsedMinutes = Math.round((w.now() - startAt) / MIN);
  assert.deepEqual(w.github.merges, issues.map(n => prs.get(n).number), 'all 4 PRs merged in exact claim order');
  // 4 PRs: PR #1 merges on tick 1 (0m), PRs #2..#4 each refresh in the tick the previous PR merged, start suite next tick, and merge on the tick after (7 ticks = 60m total, vs 14 ticks = 130m before!).
  assert.ok(ticks <= 7, `expected at most 7 ticks for 4 merges with base refresh + label lag, got ${ticks} ticks (${elapsedMinutes}m)`);
});
