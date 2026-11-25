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

function extractWorkflowScript(tag = 'NODE') {
  const yaml = readFileSync(WORKFLOW_PATH, 'utf8');
  const match = new RegExp(`node --input-type=module <<'${tag}'\\n([\\s\\S]*?)\\n\\s*${tag}\\b`).exec(yaml);
  assert.ok(match, `workflow contains inline ESM script (${tag})`);
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

  const ops = [];
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
          ops.push(`PATCH:${num}:${patch.state}`);
          Object.assign(iss, patch);
        }
        return send(200, iss);
      }
      if (req.method === 'POST' && (m = new RegExp(`^/repos/${repo}/issues/(\\d+)/comments$`).exec(url.pathname))) {
        const num = Number(m[1]);
        const iss = issues.get(num);
        const note = JSON.parse(raw);
        ops.push(`COMMENT:${num}`);
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

  // Comment is always posted strictly BEFORE closing each open issue (preventing silent closes).
  for (const closedNum of [108, 112, 401]) {
    const commentIdx = ops.indexOf(`COMMENT:${closedNum}`);
    const patchIdx = ops.indexOf(`PATCH:${closedNum}:closed`);
    assert.ok(commentIdx !== -1 && patchIdx !== -1 && commentIdx < patchIdx, `issue #${closedNum} must comment before PATCH close (${ops.join(', ')})`);
  }
});

async function runInlineScript(t, scriptTag, eventPayload, handler, repo = 'acme/widgets') {
  const server = createServer((req, res) => {
    let raw = '';
    req.on('data', chunk => { raw += chunk; });
    req.on('end', () => {
      const url = new URL(req.url, 'http://127.0.0.1');
      const send = (code, body) => {
        res.writeHead(code, { 'Content-Type': 'application/json' });
        res.end(body === null ? '' : JSON.stringify(body));
      };
      handler({ method: req.method, url, raw, body: raw ? JSON.parse(raw) : null }, send);
    });
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  t.after(() => server.close());
  const { port } = server.address();

  const dir = mkdtempSync(join(tmpdir(), 'pdd-close-guard-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const eventPath = join(dir, 'event.json');
  writeFileSync(eventPath, JSON.stringify(eventPayload));

  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, ['--input-type=module', '-e', extractWorkflowScript(scriptTag)], {
      env: {
        ...process.env,
        GH_TOKEN: 'test-token',
        REPO: repo,
        GITHUB_EVENT_PATH: eventPath,
        GITHUB_API_URL: `http://127.0.0.1:${port}`,
      },
    });
    let stdout = '', stderr = '';
    child.stdout.on('data', chunk => { stdout += chunk; });
    child.stderr.on('data', chunk => { stderr += chunk; });
    child.on('error', reject);
    child.on('close', status => resolve({ status, stdout, stderr }));
  });
}

test('AC4: close-issues aborts before closing when posting the close comment fails (no silent close)', async t => {
  const repo = 'acme/widgets';
  const iss = { number: 77, state: 'open', labels: [], comments: [] };
  const ops = [];
  const run = await runInlineScript(t, 'NODE', {
    pull_request: {
      number: 91,
      merged: true,
      merge_commit_sha: 'a'.repeat(40),
      head: { ref: 'feat/fix-77', sha: 'b'.repeat(40), repo: { full_name: repo } },
      base: { ref: 'main', sha: 'c'.repeat(40), repo: { full_name: repo } },
      body: 'Closes #77',
    },
  }, (req, send) => {
    if (req.method === 'GET' && req.url.pathname === `/repos/${repo}/pulls`) return send(200, []);
    if (req.method === 'GET' && req.url.pathname === `/repos/${repo}/issues/77`) return send(200, iss);
    if (req.method === 'POST' && req.url.pathname === `/repos/${repo}/issues/77/comments`) {
      ops.push('COMMENT:500');
      return send(500, { message: 'Internal Server Error' });
    }
    if (req.method === 'PATCH' && req.url.pathname === `/repos/${repo}/issues/77`) {
      ops.push('PATCH:closed');
      Object.assign(iss, req.body);
      return send(200, iss);
    }
    return send(404, { message: `Unhandled ${req.method} ${req.url.pathname}` });
  }, repo);

  assert.equal(run.status, 1);
  assert.deepEqual(ops, ['COMMENT:500']);
  assert.equal(iss.state, 'open', 'failed comment must leave issue open rather than silently closing');
});

function makeGuardFixture({
  repo = 'acme/widgets',
  targetNum = 500,
  targetClosedAt = '2026-11-24T18:25:00Z',
  actor = 'dev-agent',
  timelines = {},
  comments = {},
  graphqlPrs = {},
  recentIssues = [],
} = {}) {
  const ops = [];
  const state = {
    reopened: false,
    stateReason: null,
    addedLabels: [],
    postedComments: [],
  };
  const handler = (req, send) => {
    let m;
    if (req.method === 'POST' && req.url.pathname === '/graphql') {
      const num = req.body?.variables?.num;
      const nodes = graphqlPrs[num] ?? [];
      return send(200, { data: { repository: { issue: { closedByPullRequestsReferences: { nodes } } } } });
    }
    if (req.method === 'GET' && req.url.pathname === `/repos/${repo}/issues`) {
      return send(200, recentIssues);
    }
    if (req.method === 'GET' && (m = new RegExp(`^/repos/${repo}/issues/(\\d+)/timeline$`).exec(req.url.pathname))) {
      const page = Number(req.url.searchParams.get('page') ?? '1');
      return send(200, page === 1 ? (timelines[Number(m[1])] ?? []) : []);
    }
    if (req.method === 'GET' && (m = new RegExp(`^/repos/${repo}/issues/(\\d+)/comments$`).exec(req.url.pathname))) {
      const page = Number(req.url.searchParams.get('page') ?? '1');
      return send(200, page === 1 ? (comments[Number(m[1])] ?? []) : []);
    }
    if (req.method === 'POST' && req.url.pathname === `/repos/${repo}/issues/${targetNum}/comments`) {
      ops.push('COMMENT');
      state.postedComments.push(req.body.body);
      return send(201, { id: 99, body: req.body.body });
    }
    if (req.method === 'POST' && req.url.pathname === `/repos/${repo}/issues/${targetNum}/labels`) {
      ops.push('LABEL');
      state.addedLabels.push(...(req.body.labels ?? []));
      return send(200, state.addedLabels.map(name => ({ name })));
    }
    if (req.method === 'PATCH' && req.url.pathname === `/repos/${repo}/issues/${targetNum}`) {
      ops.push(`PATCH:${req.body.state}`);
      state.reopened = req.body.state === 'open';
      state.stateReason = req.body.state_reason ?? null;
      return send(200, { number: targetNum, state: req.body.state });
    }
    return send(404, { message: `Unhandled ${req.method} ${req.url.pathname}` });
  };
  const event = {
    action: 'closed',
    sender: { login: actor },
    issue: { number: targetNum, state: 'closed', closed_at: targetClosedAt },
  };
  return { event, handler, ops, state };
}

test('AC5: guard-non-pr-close reopens and labels close-needs-proof on silent closes, weak excuses, hidden/stale/post-close Proof', async t => {
  const closedAt = '2026-11-24T18:25:00Z';
  const cases = [
    { name: 'silent close (0 comments, like #3237)', comments: [] },
    { name: 'comment without Proof:', comments: [{ created_at: '2026-11-24T18:24:58Z', body: 'Closing as obsolete after refactor.' }] },
    { name: 'weak excuse Proof: file deleted', comments: [{ created_at: '2026-11-24T18:24:58Z', body: 'Reason: obsolete\nProof: file deleted' }] },
    { name: 'empty Proof:', comments: [{ created_at: '2026-11-24T18:24:58Z', body: 'Reason: fixed\nProof:   ' }] },
    { name: 'Proof hidden inside HTML comment', comments: [{ created_at: '2026-11-24T18:24:58Z', body: '<!-- Proof: `pdd lint` exit 0 -->\nClosed.' }] },
    { name: 'Proof posted AFTER closed_at', comments: [{ created_at: '2026-11-24T18:25:05Z', body: 'Reason: fixed\nProof: `pdd lint --local` -> exit 0' }] },
    {
      name: 'stale Proof posted before prior reopen',
      timeline: [
        { event: 'closed', created_at: '2026-11-15T01:00:00Z', actor: { login: 'dev-agent' } },
        { event: 'reopened', created_at: '2026-11-23T18:00:00Z', actor: { login: 'gltanaka' } },
        { event: 'closed', created_at: closedAt, actor: { login: 'dev-agent' } },
      ],
      comments: [{ created_at: '2026-11-15T00:59:00Z', body: 'Reason: fixed\nProof: `pdd lint --local` -> exit 0' }],
    },
  ];

  for (const tc of cases) {
    const fx = makeGuardFixture({
      targetNum: 3237,
      targetClosedAt: closedAt,
      timelines: { 3237: tc.timeline ?? [{ event: 'closed', created_at: closedAt, actor: { login: 'dev-agent' } }] },
      comments: { 3237: tc.comments },
    });
    const run = await runInlineScript(t, 'GUARD', fx.event, fx.handler);
    assert.equal(run.status, 0, `${tc.name}: ${run.stderr}`);
    assert.deepEqual(fx.ops, ['COMMENT', 'LABEL', 'PATCH:open'], `${tc.name}: comment -> label -> reopen order`);
    assert.equal(fx.state.reopened, true, `${tc.name}: must reopen`);
    assert.equal(fx.state.stateReason, 'reopened', `${tc.name}: state_reason`);
    assert.deepEqual(fx.state.addedLabels, ['close-needs-proof'], `${tc.name}: label`);
    assert.match(fx.state.postedComments[0], /<!-- pdd:close-guard -->/, `${tc.name}: guard marker`);
    assert.match(fx.state.postedComments[0], /no `Proof:` comment/, `${tc.name}: reason`);
  }
});

test('AC6: guard-non-pr-close allows non-PR close with valid Proof posted at/before close (within burst limit)', async t => {
  const closedAt = '2026-11-24T18:25:00Z';
  for (const body of [
    'Reason: Retired in 0.1.50.\nProof: `pdd workflow changes` on 0.1.52 -> exit 2 (`pdd workflow was removed`).',
    'Reason: Fixed in 0.1.52.\n**Proof:**\n```sh\npdd lint --local\n# Local lint: 0 errors, 0 warnings\n```',
  ]) {
    const fx = makeGuardFixture({
      targetNum: 601,
      targetClosedAt: closedAt,
      timelines: { 601: [{ event: 'closed', created_at: closedAt, actor: { login: 'Serhan-Asad' } }] },
      comments: { 601: [{ created_at: '2026-11-24T18:24:59Z', body }] },
      actor: 'Serhan-Asad',
    });
    const run = await runInlineScript(t, 'GUARD', fx.event, fx.handler);
    assert.equal(run.status, 0, run.stderr);
    assert.deepEqual(fx.ops, [], 'valid Proof within burst limit must perform zero mutations');
    assert.equal(fx.state.reopened, false);
  }
});

test('AC7: guard-non-pr-close reopens >3 non-PR closes by the same account in 10 minutes (even with valid Proof), while ignoring PR/other-actor/old closes', async t => {
  const closedAt = '2026-11-23T18:13:47Z';
  const validProofComment = [{ created_at: '2026-11-23T18:13:46Z', body: 'Reason: Retired.\nProof: `pdd workflow run` -> exit 2 (removed).' }];

  // Case A: 3 prior non-PR closes by same actor in last 10m (including one already reopened to state:open!) -> 4th trips burst guard even WITH Proof.
  const fxBurst = makeGuardFixture({
    targetNum: 3330,
    targetClosedAt: closedAt,
    actor: 'Serhan-Asad',
    timelines: {
      3330: [{ event: 'closed', created_at: closedAt, actor: { login: 'Serhan-Asad' } }],
      3596: [{ event: 'closed', created_at: '2026-11-23T18:13:24Z', actor: { login: 'Serhan-Asad' } }],
      3559: [
        { event: 'closed', created_at: '2026-11-23T18:13:26Z', actor: { login: 'Serhan-Asad' } },
        { event: 'reopened', created_at: '2026-11-23T18:13:30Z', actor: { login: 'github-actions[bot]' } },
      ],
      3531: [{ event: 'closed', created_at: '2026-11-23T18:13:28Z', actor: { login: 'Serhan-Asad' } }],
    },
    comments: { 3330: validProofComment },
    recentIssues: [
      { number: 3596, state: 'closed', closed_at: '2026-11-23T18:13:24Z' },
      { number: 3559, state: 'open', closed_at: null },
      { number: 3531, state: 'closed', closed_at: '2026-11-23T18:13:28Z' },
    ],
  });
  const runBurst = await runInlineScript(t, 'GUARD', fxBurst.event, fxBurst.handler);
  assert.equal(runBurst.status, 0, runBurst.stderr);
  assert.deepEqual(fxBurst.ops, ['COMMENT', 'LABEL', 'PATCH:open']);
  assert.equal(fxBurst.state.reopened, true);
  assert.deepEqual(fxBurst.state.addedLabels, ['close-needs-proof']);
  assert.match(fxBurst.state.postedComments[0], /burst limit exceeded \(4 non-PR closes by `@Serhan-Asad` within 10 minutes; max 3\)/);

  // Case B: 2 prior non-PR closes by same actor + 2 PR-linked closes + 1 other-actor close + 1 old (>10m) close + 1 never-closed open issue = 3 total (<= 3) -> ALLOWED.
  const fxOk = makeGuardFixture({
    targetNum: 700,
    targetClosedAt: closedAt,
    actor: 'Serhan-Asad',
    timelines: {
      700: [{ event: 'closed', created_at: closedAt, actor: { login: 'Serhan-Asad' } }],
      701: [{ event: 'closed', created_at: '2026-11-23T18:10:00Z', actor: { login: 'Serhan-Asad' } }],
      702: [{ event: 'closed', created_at: '2026-11-23T18:11:00Z', actor: { login: 'Serhan-Asad' } }],
      703: [{ event: 'closed', created_at: '2026-11-23T18:12:00Z', actor: { login: 'Serhan-Asad' } }], // PR-closed via graphqlPrs
      704: [{ event: 'closed', created_at: '2026-11-23T18:12:30Z', actor: { login: 'gltanaka' } }],    // different actor
      705: [{ event: 'closed', created_at: '2026-11-23T17:55:00Z', actor: { login: 'Serhan-Asad' } }], // >10 min ago
      706: [{ event: 'labeled', created_at: '2026-11-23T18:12:50Z', actor: { login: 'Serhan-Asad' } }], // never closed
    },
    graphqlPrs: {
      703: [{ merged: true, mergedAt: '2026-11-23T18:11:58Z' }],
    },
    comments: { 700: validProofComment },
    recentIssues: [
      { number: 701, state: 'closed', closed_at: '2026-11-23T18:10:00Z' },
      { number: 702, state: 'closed', closed_at: '2026-11-23T18:11:00Z' },
      { number: 703, state: 'closed', closed_at: '2026-11-23T18:12:00Z' },
      { number: 704, state: 'closed', closed_at: '2026-11-23T18:12:30Z' },
      { number: 705, state: 'closed', closed_at: '2026-11-23T17:55:00Z' },
      { number: 706, state: 'open', closed_at: null },
    ],
  });
  const runOk = await runInlineScript(t, 'GUARD', fxOk.event, fxOk.handler);
  assert.equal(runOk.status, 0, runOk.stderr);
  assert.deepEqual(fxOk.ops, [], '3 non-PR closes (ignoring PR/other-actor/old/never-closed) must be allowed');
});

test('AC8: guard-non-pr-close allows PR-linked closes (GraphQL merged PR or commit_id), but rejects silent re-close after a reopen', async t => {
  const closedAt = '2026-11-24T18:26:50Z';

  // Case A: Closed via merged PR (GraphQL closedByPullRequestsReferences, matching real GitHub #3469 / #3537).
  const fxGql = makeGuardFixture({
    targetNum: 3469,
    targetClosedAt: closedAt,
    timelines: { 3469: [{ event: 'closed', created_at: closedAt, actor: { login: 'Serhan-Asad' }, commit_id: null }] },
    graphqlPrs: { 3469: [{ merged: true, mergedAt: '2026-11-24T18:26:48Z' }] },
    comments: { 3469: [] },
  });
  const runGql = await runInlineScript(t, 'GUARD', fxGql.event, fxGql.handler);
  assert.equal(runGql.status, 0, runGql.stderr);
  assert.deepEqual(fxGql.ops, [], 'merged PR close via GraphQL requires no Proof comment');

  // Case B: Closed directly via commit_id in timeline.
  const fxCommit = makeGuardFixture({
    targetNum: 3470,
    targetClosedAt: closedAt,
    timelines: { 3470: [{ event: 'closed', created_at: closedAt, actor: { login: 'Serhan-Asad' }, commit_id: 'f'.repeat(40) }] },
    comments: { 3470: [] },
  });
  const runCommit = await runInlineScript(t, 'GUARD', fxCommit.event, fxCommit.handler);
  assert.equal(runCommit.status, 0, runCommit.stderr);
  assert.deepEqual(fxCommit.ops, [], 'commit_id close requires no Proof comment');

  // Case C: Old merged PR before a reopen does NOT excuse a later silent non-PR re-close.
  const fxStalePr = makeGuardFixture({
    targetNum: 3471,
    targetClosedAt: closedAt,
    timelines: {
      3471: [
        { event: 'closed', created_at: '2026-11-15T01:33:12Z', actor: { login: 'Serhan-Asad' } },
        { event: 'reopened', created_at: '2026-11-23T18:26:37Z', actor: { login: 'gltanaka' } },
        { event: 'closed', created_at: closedAt, actor: { login: 'Serhan-Asad' } },
      ],
    },
    graphqlPrs: { 3471: [{ merged: true, mergedAt: '2026-11-14T00:04:39Z' }] },
    comments: { 3471: [] },
  });
  const runStalePr = await runInlineScript(t, 'GUARD', fxStalePr.event, fxStalePr.handler);
  assert.equal(runStalePr.status, 0, runStalePr.stderr);
  assert.deepEqual(fxStalePr.ops, ['COMMENT', 'LABEL', 'PATCH:open'], 'old PR merged before reopen must not excuse silent re-close');

  // Case D: Eventual-consistency race where timeline only shows an older commit_id close before reopen -> must still reopen.
  const fxStaleCommit = makeGuardFixture({
    targetNum: 3472,
    targetClosedAt: closedAt,
    actor: 'Serhan-Asad',
    timelines: {
      3472: [
        { event: 'closed', created_at: '2026-11-15T01:33:12Z', actor: { login: 'Serhan-Asad' }, commit_id: 'e'.repeat(40) },
        { event: 'reopened', created_at: '2026-11-23T18:26:37Z', actor: { login: 'gltanaka' } },
      ],
    },
    comments: { 3472: [] },
  });
  const runStaleCommit = await runInlineScript(t, 'GUARD', fxStaleCommit.event, fxStaleCommit.handler);
  assert.equal(runStaleCommit.status, 0, runStaleCommit.stderr);
  assert.deepEqual(fxStaleCommit.ops, ['COMMENT', 'LABEL', 'PATCH:open'], 'stale commit_id before reopen must not bypass guard');
});
