import assert from 'node:assert/strict';
import test from 'node:test';
import { writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { handoffFixture } from './helpers/bounded-area-handoff.mjs';

// Independent specification oracle: enumerate complete candidates, rather than
// reuse the implementation's clipping or line-fitting algorithm.
const ITEM_LIMIT = 1024;
const LINE_LIMIT = 8192;
const SHORTENED = ' … [summary shortened; read ledger]';
const PREFIX = 'Approved so far: ';
const bytes = text => Buffer.byteLength(text, 'utf8');

function normalize(summary) {
  return String(summary || '').replace(/\s+/gu, ' ').trim().replace(/[.\s]+$/gu, '') || 'done';
}

function specifiedItem(step, summary) {
  const original = `${step}: ${normalize(summary)}`;
  if (bytes(original) <= ITEM_LIMIT) return original;
  const points = Array.from(original);
  const allowed = [];
  for (let count = 0; count <= points.length; count += 1) {
    const candidate = points.slice(0, count).join('') + SHORTENED;
    if (bytes(candidate) <= ITEM_LIMIT) allowed.push(candidate);
  }
  return allowed.at(-1);
}

function specifiedLine(entries) {
  const items = entries.map(([step, summary]) => specifiedItem(step, summary));
  if (!items.length) return `${PREFIX}no step summaries.`;
  const allowed = [];
  for (let count = 0; count <= items.length; count += 1) {
    const parts = items.slice(0, count);
    if (count < items.length) {
      parts.push(`[${items.length - count} further step summaries omitted; read ledger]`);
    }
    const line = PREFIX + parts.join('; ') + '.';
    if (bytes(line) <= LINE_LIMIT) allowed.push({ count, line });
  }
  return allowed.at(-1).line;
}

function fillBytes(pattern, count) {
  // Place any ASCII remainder first so the clipping edge still crosses the
  // repeated Unicode pattern, including a possible combining-mark boundary.
  const copies = Math.floor(count / bytes(pattern));
  return 'a'.repeat(count - copies * bytes(pattern)) + pattern.repeat(copies);
}

function itemOfSize(step, pattern, target) {
  return fillBytes(pattern, target - bytes(`${step}: `));
}

function itemCases() {
  const cases = [];
  for (const step of ['x', 'n'.repeat(64)]) {
    for (const pattern of ['a', 'é', '界', '😀', 'e\u0301', 'aé界😀e\u0301']) {
      for (let target = 1022; target <= 1026; target += 1) {
        cases.push({ name: `label-${step.length}/pattern-${JSON.stringify(pattern)}/bytes-${target}`,
          entries: [[step, itemOfSize(step, pattern, target)]] });
      }
    }
  }
  return cases;
}

function aggregateCases() {
  const cases = [];
  const counts = [...Array.from({ length: 13 }, (_, count) => count), 15, 16, 17, 18, 98, 99, 100, 106, 107, 108];
  for (const count of counts) {
    const entries = Array.from({ length: count }, (_, index) => {
      const step = `s${String(index).padStart(3, '0')}`;
      return [step, itemOfSize(step, 'é界😀', 1024)];
    });
    cases.push({ name: `aggregate-max-items-${count}`, entries });
  }
  for (let delta = -2; delta <= 2; delta += 1) {
    const entries = Array.from({ length: 8 }, (_, index) => {
      const step = `b${index}`;
      const target = index < 7 ? 1024 : LINE_LIMIT + delta - bytes(PREFIX) - 1 - 14 - 7 * 1024;
      return [step, itemOfSize(step, 'a', target)];
    });
    cases.push({ name: `aggregate-equality-offset-${delta}`, entries });
  }
  // A large item cannot be skipped to retain a later tiny item. Shortening an
  // item that is then omitted also must not change the omission count.
  cases.push({ name: 'mixed-order-no-skip', entries: Array.from({ length: 19 }, (_, index) => {
    const step = `m${index}`;
    return [step, itemOfSize(step, index % 2 ? '😀' : 'a', index < 8 || index % 3 === 0 ? 1026 : 20)];
  }) });
  return cases;
}

test('formal: 89 bounded public handoffs preserve byte limits, maximal prefixes and workflow order', async t => {
  const cases = [...itemCases(), ...aggregateCases()];
  assert.equal(cases.length, 89, 'the recorded finite domain must stay explicit');
  const steps = [...new Set(cases.flatMap(({ entries }) => entries.map(([step]) => step)))];
  const f = await handoffFixture(t, { steps });
  await f.start();
  // Establish a real approval/open transition before reusing its native public
  // replacement operation. Each matrix input then supplies historical ledger
  // records; no formatter or private summary helper is called by this test.
  for (const step of steps) await f.done(step, 'fixture seed');
  const approval = await f.approve();
  assert.equal(approval.exitCode, 0, approval.message);
  const completed = structuredClone(f.record().done);
  const statusPath = join(f.source, '.git', 'pdd', 'runs', '17', 'status.json');
  let checked = 0;
  for (const { name, entries } of cases) {
    const seeded = f.record();
    seeded.done = Object.fromEntries(entries.map(([step, summary]) => [step, { ...completed[step], summary }]));
    writeFileSync(statusPath, JSON.stringify(seeded));
    const originalDone = structuredClone(seeded.done);
    const originalAuthority = Object.fromEntries(['area', 'gate', 'question', 'approvalRecord'].map(key => [key, seeded[key]]));
    const opened = await f.open({ newSession: true });
    assert.equal(opened.exitCode, 0, `${name}: ${opened.message}`);
    const lines = f.brief().split('\n').filter(line => line.startsWith(PREFIX));
    assert.equal(lines.length, 1, `${name}: exactly one delivered earlier-summary line`);
    const actual = lines[0];
    assert.ok(bytes(actual) <= LINE_LIMIT, `${name}: aggregate cap exceeded (${bytes(actual)} UTF-8 bytes)`);
    if (entries.length === 1) {
      const item = actual.slice(PREFIX.length, -1);
      assert.ok(bytes(item) <= ITEM_LIMIT, `${name}: per-item cap exceeded (${bytes(item)} UTF-8 bytes)`);
    }
    assert.ok(actual.isWellFormed(), `${name}: split Unicode surrogate`);
    assert.ok(!actual.includes('\uFFFD'), `${name}: replacement character inserted`);
    assert.equal(Buffer.from(actual, 'utf8').toString('utf8'), actual, `${name}: invalid UTF-8`);
    assert.equal(actual, specifiedLine(entries), `${name}: maximal whole-prefix/ordered-item oracle`);
    const after = f.record();
    assert.deepEqual(after.done, originalDone, `${name}: durable completed records changed`);
    assert.deepEqual(Object.fromEntries(Object.keys(originalAuthority).map(key => [key, after[key]])), originalAuthority,
      `${name}: preview granted authority or advanced workflow`);
    checked += 1;
  }
  assert.equal(checked, 89);
  t.diagnostic(`FORMAL BOUNDED: ${checked} actual public openRun replacements; 60 item cases + 29 aggregate cases; one real approveRun transition; ${steps.length} workflow steps; all original done records preserved.`);
});
