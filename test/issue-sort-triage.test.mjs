import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { fixture, key, repository } from './helpers/issue-sort-fixture.mjs';
const rows = JSON.parse(readFileSync(new URL('./fixtures/issue-sort-cases.json', import.meta.url))).rows;
for (const row of rows) test(`manual triage ${row.number} derives ${row.expected}`, async () => {
  const w = fixture([row.number], { context: { release: '0.1.20', areas: [
    { name: 'cli', owner: 'autopilot', match: { paths: ['src/**'] } },
    { name: 'runtime', owner: 'agarwal-ishaan', match: { repositories: ['promptdriven/prompt-runtime'] } },
  ] } });
  const r = w.record(row.number, {
    belongs: { kind: row.belongs === 'old-pdd' ? 'old-code' : row.belongs === 'runtime' ? 'repository' : 'area', area: row.belongs === 'runtime' ? 'runtime' : 'cli', repository: row.belongs === 'runtime' ? 'promptdriven/prompt-runtime' : '' },
    status: { state: row.status, release: '0.1.20', fix: row.status === 'fixed' ? row.evidence : '', evidence: [row.evidence] },
    genuine: { kind: row.genuine, duplicateOf: row.duplicate ? `https://github.com/promptdriven/pdd/issues/${row.duplicate}` : '', reason: row.belongs === 'old-pdd' || row.genuine === 'not-genuine' ? row.evidence : '' },
    paths: row.belongs === 'runtime' ? [] : ['src/cli.mjs'],
    rootCause: row.rootCause, severity: row.severity,
    question: row.expected === 'question' ? 'Which product behavior should this issue require?' : '',
  });
  w.save(r); w.review(row.number);
  const snapshot = (await readDependencySnapshot({ repository }, w.ports)).snapshot;
  const node = projectIssueGraph({ snapshot }).nodes.find(x => x.key === key(row.number));
  assert.equal(node.sort?.action, row.expected);
  assert.equal(node.eligible, row.expected === 'work');
});
