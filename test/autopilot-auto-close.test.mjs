import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { workflowRunsOnPr } from '../src/autopilot-core.mjs';
import { coreWorld } from './helpers/core-world.mjs';

const WORKFLOW_PATH = fileURLToPath(new URL('../.github/workflows/close-merged-issues.yml', import.meta.url));

function extractWorkflowScript() {
  const yaml = readFileSync(WORKFLOW_PATH, 'utf8');
  const match = /node --input-type=module <<'NODE'\n([\s\S]*?)\n\s*NODE\b/.exec(yaml);
  assert.ok(match, 'workflow contains inline ESM script');
  return match[1].replace(/^ {10}/gm, '');
}

test('AC1: observe mode prepends Fixes #N before the Autopilot evidence block once when missing, and respects Refs / Part of / Not fixed yet', async t => {
  const w = await coreWorld(t, { settings: { mode: 'observe', runs: 2 } });
  w.issue(17);
  w.issue(18);
  await w.tick();

  // #17 has only heading/newline, fenced, HTML-commented, and zero-width-inert words -> Autopilot adds real Fixes #17.
  const { pr: pr17 } = w.build(17, {
    body: '## Fix\n\n#17 reported a crash.\n\n```\nFixes #17\n```\n<!-- Closes #17 -->\nFix\u200b #17\n\nRuntime: PASS',
  });
  // #18 explicitly marks partial work inside a comma list ("Refs #10, #18") -> Autopilot must not inject Fixes #18.
  const { pr: pr18 } = w.build(18, {
    body: 'Refs #10, #18\n\nRuntime: PASS',
  });
  await w.tick();
  w.review(17, 'PASS'); w.suite(17, 0);
  w.review(18, 'PASS'); w.suite(18, 0);
  await w.tick();

  const outsideFence17 = pr17.body.split('```').at(-1).split('<!-- pdd:autopilot-core:evidence:start -->')[0];
  assert.match(outsideFence17, /\bFixes #17\b/);
  assert.equal((outsideFence17.match(/\bFixes #17\b/g) ?? []).length, 1);
  assert.ok(w.labels(17).includes('pdd:would-merge'));

  assert.doesNotMatch(pr18.body, /\b(?:Fixes|Closes|Resolves)[ \t]+#18\b/i);
  assert.match(pr18.body, /<!-- pdd:autopilot-core:evidence:start -->/);
  assert.ok(w.labels(18).includes('pdd:would-merge'));
});

test('AC2: sweepWouldMerge closes merged observe-mode issues, keeps reopened issues (without a new PR) and partial PRs open, and cleans pdd:would-merge', async t => {
  const w = await coreWorld(t, { settings: { mode: 'observe', runs: 2 } });
  w.issue(17);
  w.issue(18);
  await w.tick();

  const { pr: pr17 } = w.build(17, { body: 'Summary without keyword.\n\nRuntime: PASS' });
  const { pr: pr18 } = w.build(18, { body: 'Part of #18\n\nRuntime: PASS' });
  await w.tick();
  w.review(17, 'PASS'); w.suite(17, 0);
  w.review(18, 'PASS'); w.suite(18, 0);
  await w.tick();

  // Case A: Person merges both PRs on GitHub without closing the issues natively -> #17 closes, #18 (Part of) stays open, both drop pdd:would-merge.
  pr17.state = 'closed'; pr17.merged = true;
  pr18.state = 'closed'; pr18.merged = true;
  await w.tick();

  assert.equal(w.github.issues.get(17).state, 'closed');
  assert.ok(!w.labels(17).includes('pdd:would-merge'));
  assert.equal(w.github.issues.get(18).state, 'open');
  assert.ok(!w.labels(18).includes('pdd:would-merge'));

  // Case B: GitHub closed an issue natively via Fixes #N (leaving pdd:would-merge attached), and a person later reopens #17 BEFORE any new PR exists.
  // sweepWouldMerge must NOT re-close the reopened issue; it only removes the stale pdd:would-merge label.
  w.github.label(17, 'pdd:would-merge');
  w.github.close(17);
  w.advance(5000);
  await w.gh(['api', '--include', '--method', 'PATCH', 'repos/acme/widgets/issues/17'], { input: JSON.stringify({ state: 'open' }) });
  assert.equal(w.github.issues.get(17).state, 'open');
  assert.ok(w.labels(17).includes('pdd:would-merge'));

  await w.tick();
  assert.equal(w.github.issues.get(17).state, 'open', 'reopened issue without a new PR must remain open');
  assert.ok(!w.labels(17).includes('pdd:would-merge'), 'stale pdd:would-merge label is cleaned up');
});

test('AC3: close-merged-issues workflow is ignored as PR CI and closes comma-list and newly-merged sub-PR issues safely', async t => {
  const yaml = readFileSync(WORKFLOW_PATH, 'utf8');
  assert.equal(workflowRunsOnPr(yaml, 'pdd/core-17-abc', 'main', ['src/autopilot-core.mjs']), false);

  const repo = 'acme/widgets';
  const baseSha = '1'.repeat(40), headSha = '2'.repeat(40), mergeSha = '3'.repeat(40);
  const subNewSha = '4'.repeat(40), subOldSha = '5'.repeat(40), subPartialSha = '6'.repeat(40), subMissingBaseSha = '7'.repeat(40);

  const issues = new Map([
    [12, { number: 12, state: 'open', labels: [], comments: [] }],
    [104, { number: 104, state: 'closed', labels: [{ name: 'pdd:would-merge' }, { name: 'pdd:working' }, { name: 'bug' }], comments: [] }],
    [108, { number: 108, state: 'open', labels: [{ name: 'pdd:working' }], comments: [] }],
    [112, { number: 112, state: 'open', labels: [], comments: [] }],
    [200, { number: 200, state: 'open', labels: [], comments: [] }],
    [201, { number: 201, state: 'open', repository_url: 'https://api.github.com/repos/other/widgets', labels: [], comments: [] }],
    [300, { number: 300, state: 'open', labels: [], comments: [] }],
    [401, { number: 401, state: 'open', labels: [{ name: 'pdd:would-merge' }], comments: [] }],
    [402, { number: 402, state: 'open', labels: [], comments: [] }],
    [403, { number: 403, state: 'open', labels: [], comments: [] }],
    [404, { number: 404, state: 'open', labels: [], comments: [] }],
    [405, { number: 405, state: 'open', labels: [], comments: [] }],
    [406, { number: 406, state: 'open', labels: [], comments: [] }],
  ]);

  const subPrs = [
    {
      number: 51, merged_at: '2026-11-12T10:00:00Z', merge_commit_sha: subNewSha,
      head: { repo: { full_name: repo } },
      body: 'Fixes #401',
    },
    {
      number: 52, merged_at: '2026-10-01T10:00:00Z', merge_commit_sha: subOldSha,
      head: { repo: { full_name: repo } },
      body: 'Fixes #402',
    },
    {
      number: 53, merged_at: '2026-11-12T10:05:00Z', merge_commit_sha: subPartialSha,
      head: { repo: { full_name: repo } },
      body: 'Not fixed yet: reproduces the race.\n\nFixes #403\nRefs #404',
    },
    {
      number: 54, merged_at: '2026-11-12T10:06:00Z', merge_commit_sha: subNewSha,
      head: { repo: { full_name: 'forker/widgets' } },
      body: 'Fixes #405',
    },
    {
      number: 55, merged_at: '2026-11-12T10:07:00Z', merge_commit_sha: subMissingBaseSha,
      head: { repo: { full_name: repo } },
      body: 'Fixes #406',
    },
  ];

  const compares = new Map([
    [`${subNewSha}...${headSha}`, { status: 'ahead', ahead_by: 2, behind_by: 0 }],
    [`${baseSha}...${subNewSha}`, { status: 'ahead', ahead_by: 1, behind_by: 0 }],
    [`${subOldSha}...${headSha}`, { status: 'ahead', ahead_by: 5, behind_by: 0 }],
    [`${baseSha}...${subOldSha}`, { status: 'behind', ahead_by: 0, behind_by: 3 }],
    [`${subPartialSha}...${headSha}`, { status: 'identical', ahead_by: 0, behind_by: 0 }],
    [`${baseSha}...${subPartialSha}`, { status: 'ahead', ahead_by: 1, behind_by: 0 }],
    [`${subMissingBaseSha}...${headSha}`, { status: 'ahead', ahead_by: 1, behind_by: 0 }],
    // Intentionally omit `${baseSha}...${subMissingBaseSha}` (404) -> must fail closed and leave #406 open.
  ]);

  const server = createServer((req, res) => {
    let raw = '';
    req.on('data', chunk => { raw += chunk; });
    req.on('end', () => {
      const url = new URL(req.url, 'http://127.0.0.1');
      const send = (code, body) => {
        res.writeHead(code, { 'Content-Type': 'application/json' });
        res.end(body === null ? '' : JSON.stringify(body));
      };
      if (req.method === 'GET' && url.pathname === `/repos/${repo}/pulls`) {
        const page = Number(url.searchParams.get('page') ?? '1');
        return send(200, page === 1 && url.searchParams.get('base') === 'pdd/release-0130-integrate' ? subPrs : []);
      }
      let m;
      if (req.method === 'GET' && (m = new RegExp(`^/repos/${repo}/compare/(.+)$`).exec(url.pathname))) {
        const cmp = compares.get(m[1]);
        return cmp ? send(200, cmp) : send(404, { message: 'Not Found' });
      }
      if ((m = new RegExp(`^/repos/${repo}/issues/(\\d+)$`).exec(url.pathname))) {
        const num = Number(m[1]);
        if (num === 999) return send(410, { message: 'Gone' });
        const iss = issues.get(num);
        if (!iss) return send(404, { message: 'Not Found' });
        if (req.method === 'PATCH') {
          const patch = JSON.parse(raw);
          Object.assign(iss, patch);
        }
        return send(200, iss);
      }
      if (req.method === 'POST' && (m = new RegExp(`^/repos/${repo}/issues/(\\d+)/comments$`).exec(url.pathname))) {
        const iss = issues.get(Number(m[1]));
        const note = JSON.parse(raw);
        iss.comments.push(note.body);
        return send(201, { id: 1, body: note.body });
      }
      if (req.method === 'DELETE' && (m = new RegExp(`^/repos/${repo}/issues/(\\d+)/labels/(.+)$`).exec(url.pathname))) {
        const iss = issues.get(Number(m[1])), label = decodeURIComponent(m[2]);
        iss.labels = iss.labels.filter(l => l.name !== label);
        return send(200, iss.labels);
      }
      return send(404, { message: `Unhandled ${req.method} ${url.pathname}` });
    });
  });

  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  t.after(() => server.close());
  const { port } = server.address();

  const dir = mkdtempSync(join(tmpdir(), 'pdd-close-wf-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const eventPath = join(dir, 'event.json');
  writeFileSync(eventPath, JSON.stringify({
    pull_request: {
      number: 90,
      merged: true,
      merge_commit_sha: mergeSha,
      head: { ref: 'pdd/release-0130-integrate', sha: headSha, repo: { full_name: repo } },
      base: { ref: 'main', sha: baseSha, repo: { full_name: repo } },
      body: [
        'Closes #104, #999, #201, #108, and https://github.com/acme/widgets/issues/112',
        'and #200 stays open on the next line',
        '## Fix',
        '',
        '#300 reported a similar symptom',
        'Fixes #12ef00',
        '`multiline',
        'Fixes #300`',
        'Refs #200',
        'Closes other/widgets#300 and my-acme/widgets#300',
        '```',
        'Fixes #300',
        '```',
        '<!-- Resolves #300 -->',
        'Fix\u200b #300',
      ].join('\r\n'),
    },
  }));

  const run = await new Promise((resolve, reject) => {
    const child = spawn(process.execPath, ['--input-type=module', '-e', extractWorkflowScript()], {
      env: {
        ...process.env,
        GH_TOKEN: 'test-token',
        REPO: repo,
        GITHUB_EVENT_PATH: eventPath,
        GITHUB_API_URL: `http://127.0.0.1:${port}`,
      },
    });
    let stderr = '';
    child.stderr.on('data', chunk => { stderr += chunk; });
    child.on('error', reject);
    child.on('close', status => resolve({ status, stderr }));
  });
  assert.equal(run.status, 0, run.stderr);

  // #104 was already closed natively by GitHub -> no extra comment, stale pdd labels removed, 'bug' kept.
  assert.equal(issues.get(104).state, 'closed');
  assert.deepEqual(issues.get(104).comments, []);
  assert.deepEqual(issues.get(104).labels.map(l => l.name), ['bug']);

  // #108 and #112 closed from the comma/and list even after #999 returned 410 Gone and #201 was transferred.
  assert.equal(issues.get(108).state, 'closed');
  assert.equal(issues.get(108).state_reason, 'completed');
  assert.deepEqual(issues.get(108).labels, []);
  assert.equal(issues.get(108).comments.length, 1);
  assert.equal(issues.get(112).state, 'closed');

  // #401 closed from newly-merged sub-PR #51; stale pdd:would-merge removed.
  assert.equal(issues.get(401).state, 'closed');
  assert.deepEqual(issues.get(401).labels, []);
  assert.match(issues.get(401).comments[0], /pull\/90.*pull\/51/);

  // Non-targets all remain open.
  for (const keepOpen of [12, 200, 201, 300, 402, 403, 404, 405, 406]) {
    assert.equal(issues.get(keepOpen).state, 'open', `issue #${keepOpen} must remain open`);
  }
});
