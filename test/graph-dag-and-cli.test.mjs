import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import {
  issueKey,
  projectIssueGraph,
  topologicalWaves,
  validateDependencyChange,
  wouldCreateCycle,
} from '../src/autopilot/graph/dag.mjs';
import { readIssueGraph, refreshIssueGraph, runIssueGraph } from '../src/autopilot/graph/cli.mjs';
import { renderIssueGraph } from '../src/autopilot/graph/view.mjs';
import * as legacyGraphFacade from '../src/issue-dependency-graph.mjs';
import * as legacyViewFacade from '../src/issue-dependency-graph-view.mjs';
import * as legacyDagFacade from '../src/issue-dependencies.mjs';

const REPO = 'example/crm';
const k = n => `https://github.com/${REPO}/issues/${n}`;

function makeSnapshot(overrides = {}) {
  return {
    repository: REPO,
    capturedAt: '2026-11-21T12:00:00.000Z',
    complete: true,
    issues: [
      { key: k(1), nodeId: '101', title: 'Base schema', revision: 'r1', state: 'open', authority: 'trusted', conditions: [], execution: 'idle', holds: [], assignees: [] },
      { key: k(2), nodeId: '102', title: 'API route', revision: 'r2', state: 'open', authority: 'trusted', conditions: [], execution: 'idle', holds: [], assignees: [] },
      { key: k(3), nodeId: '103', title: 'UI screen', revision: 'r3', state: 'open', authority: 'trusted', conditions: [], execution: 'idle', holds: [], assignees: [] },
    ],
    edges: [
      { dependent: k(2), blocker: k(1) },
      { dependent: k(3), blocker: k(2) },
    ],
    reviews: [],
    impacts: [],
    inputs: [],
    ...overrides,
  };
}

test('src/autopilot/graph modules stay <= 380L and contain zero legacy workflow imports', () => {
  for (const rel of ['../src/autopilot/graph/dag.mjs', '../src/autopilot/graph/cli.mjs', '../src/autopilot/graph/view.mjs']) {
    const src = readFileSync(fileURLToPath(new URL(rel, import.meta.url)), 'utf8');
    const lines = src.split('\n').length;
    assert.ok(lines <= 380, `${rel} is ${lines}L (expected <= 380L)`);
    assert.doesNotMatch(src, /workflow-/, `${rel} must not import legacy workflow modules`);
  }
  assert.equal(legacyGraphFacade.runIssueGraph, runIssueGraph);
  assert.equal(legacyViewFacade.renderIssueGraph, renderIssueGraph);
  assert.equal(legacyDagFacade.projectIssueGraph, projectIssueGraph);
});

test('dag.mjs validates cycles, projects graph states, and computes topological waves', () => {
  const snapshot = makeSnapshot();
  assert.equal(issueKey('https://github.com/Example/CRM/issues/42'), k(42));
  const graph = projectIssueGraph({ snapshot });
  assert.equal(graph.nodes.length, 3);
  assert.equal(graph.nodes.find(n => n.key === k(1)).dependencyState, 'clear');
  assert.equal(graph.nodes.find(n => n.key === k(2)).dependencyState, 'waiting');

  assert.deepEqual(validateDependencyChange({ snapshot, dependent: k(1), blocker: k(3) }), { allowed: false, reason: 'cycle' });
  assert.deepEqual(validateDependencyChange({ snapshot, dependent: k(3), blocker: k(1) }), { allowed: true, reason: 'ok' });
  assert.equal(wouldCreateCycle(snapshot.edges, k(1), k(3)), true);
  assert.equal(wouldCreateCycle(snapshot.edges, k(3), k(1)), false);

  const waves = topologicalWaves([k(1), k(2), k(3)], snapshot.edges);
  assert.deepEqual(waves, { waves: [[k(1)], [k(2)], [k(3)]], cyclic: [] });
});

test('cli.mjs refreshes cache-free text view, respects headless handoff, and renders inert view HTML', async () => {
  let saved = '';
  const snapshot = makeSnapshot();
  const ports = {
    cache: {
      read: async () => ({ json: saved }),
      write: async ({ json }) => { saved = json; return { ok: true }; },
    },
    snapshots: { read: async () => ({ snapshot }) },
    refresh: { schedule: async () => ({ ok: true }) },
    host: { read: async () => ({ headless: true }) },
  };
  const refreshed = await refreshIssueGraph({ cwd: '', repository: REPO }, ports);
  assert.equal(refreshed.sync, 'current');
  assert.ok(saved.includes(k(2)));

  const cached = await readIssueGraph({ cwd: '', repository: REPO }, ports);
  assert.equal(cached.sync, 'refreshing');
  assert.equal(cached.graph.nodes.length, 3);

  const openHeadless = await runIssueGraph({ cwd: '', repository: REPO, issue: '2', open: true }, ports);
  assert.equal(openHeadless.exitCode, 0);
  assert.equal(openHeadless.handoff, `pdd graph --open --repo ${REPO} --issue 2`);
  assert.match(openHeadless.message, /Blocker: https:\/\/github\.com\/example\/crm\/issues\/1/);

  const rendered = renderIssueGraph({ graph: refreshed.graph, repository: REPO, query: '', filter: 'waiting', selected: k(2), sync: 'current', lastSync: snapshot.capturedAt });
  assert.deepEqual(rendered.visible, [k(2), k(3)]);
  assert.deepEqual(rendered.context, [k(1)]);
  assert.match(rendered.html, /#2 API route/);
});
