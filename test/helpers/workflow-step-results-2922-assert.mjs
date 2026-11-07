import assert from 'node:assert/strict';
import { cases } from './workflow-step-results-2922-fixture.mjs';

const identity = row => `${row.area}/${row.step}`;
// Requirement-authored formatting for the frozen records, following the existing
// results-reader contract. Never derived from a product renderer or its output.
export const checkLines = [
  'pdd result: pdd lint (batch synthetic-first, 1970-01-01T00:00:02Z, request synthetic-first-request): SYNTHETIC-2922-FIRST: supplied result; no check executed.',
  'pdd result: pdd lint (batch synthetic-second, 1970-01-01T00:00:02Z, requests synthetic-second-request synthetic-third-request): SYNTHETIC-2922-SECOND: supplied result; no check executed.'
];
export const noneLine = 'pdd result: none. pdd has no pdd test, pdd lint or pdd workflow prove result of its own for this run (pdd:no-verdict).';

export function assertJson(reply) {
  assert.equal(reply.exitCode, cases.expected.exitCode);
  const doc = JSON.parse(reply.message); // The entire message, not a JSON substring.
  const selected = doc.runs.filter(row => row.repo === cases.expected.selectedRun.repo && row.number === cases.expected.selectedRun.number);
  assert.equal(selected.length, 1, 'Select the run by repository and issue');
  const run = selected[0];
  assert.equal(run.area, cases.expected.selectedRun.currentArea);
  assert.ok(Array.isArray(run.steps), '2922: JSON must project saved step results');
  const byIdentity = new Map(run.steps.map(row => [identity(row), row]));
  assert.equal(byIdentity.size, run.steps.length, 'No duplicate step identity');
  assert.deepEqual([...byIdentity.keys()].sort(), cases.expected.byStep.map(identity).sort());
  for (const expected of cases.expected.byStep) {
    const row = byIdentity.get(identity(expected));
    assert.ok(Object.hasOwn(row, 'pddResults'), `2922: ${identity(expected)} needs its own explicit result list`);
    assert.deepEqual(row.pddResults, expected.pddResults, `2922: complete ordered saved payload for ${identity(expected)}`);
  }
  return run;
}

export function textSections(message) {
  const sections = new Map(); let current = null;
  for (const line of message.split('\n')) {
    const label = /^Step: ([^\r\n]+) \/ ([^\r\n]+)$/.exec(line);
    if (label) {
      current = `${label[1]}/${label[2]}`;
      assert.ok(!sections.has(current), `Duplicate step section: ${current}`);
      sections.set(current, []);
    } else if (current && line.startsWith('  ')) sections.get(current).push(line.slice(2));
    else current = null; // A result cannot leak across the next section/field.
  }
  return sections;
}

export function assertText(reply) {
  assert.equal(reply.exitCode, cases.expected.exitCode);
  assert.ok(reply.message.includes(`${cases.expected.selectedRun.repo}#${cases.expected.selectedRun.number}`));
  const sections = textSections(reply.message);
  assert.deepEqual([...sections.keys()].sort(), cases.expected.byStep.map(identity).sort(), '2922: each owning area/step has a bounded result section');
  for (const row of cases.expected.byStep) {
    const lines = sections.get(identity(row)).filter(line => line.startsWith('pdd result:'));
    assert.deepEqual(lines, row.pddResults.length ? checkLines : [noneLine], `2922: saved results for ${identity(row)} (agent notes cannot substitute)`);
  }
}

// Semantic controls use independent requirement-authored satisfying displays;
// corruptions are applied only to observations, never to saved state or vectors.
export function satisfyingJson() {
  return { runs: [{ repo: cases.expected.selectedRun.repo, number: cases.expected.selectedRun.number,
    area: cases.expected.selectedRun.currentArea, prs: [], steps: structuredClone(cases.expected.byStep).map(({ area, step, pddResults }) => ({ area, step, pddResults })) }] };
}
export function satisfyingText() {
  return [`${cases.expected.selectedRun.repo}#${cases.expected.selectedRun.number}`, 'Gate: none',
    ...cases.expected.byStep.flatMap(row => [`Step: ${row.area} / ${row.step}`,
      ...(row.pddResults.length ? checkLines : [noneLine]).map(line => `  ${line}`),
      `  Agent note — not checked by pdd: ${cases.input.selectedRun.done[row.step].summary}`])].join('\n');
}
