// A small offline world for the Autopilot core tick: a fake GitHub (one work repository and the
// promptdriven/pdd report repository), a real local Git origin and clone, a fake clock and a scripted
// agent job runner. No network, no real agent, no timer.
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, existsSync, statSync, appendFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { execFileSync, spawnSync } from 'node:child_process';
import { createGithubRepoFake } from './github-repo-fake.mjs';
import { tickCore, coreSettings } from '../../src/autopilot-core.mjs';

const endpointOf = args => args.find((word, index) => index > 0 && /^repos\//.test(word));
const methodOf = args => (args.includes('--method') ? args[args.indexOf('--method') + 1] : 'GET').toUpperCase();
const ok = (status, body) => ({ code: status < 300 ? 0 : 1, stdout: `HTTP/2.0 ${status} OK\r\nX-Ratelimit-Remaining: 4000\r\n\r\n${JSON.stringify(body)}`, stderr: status < 300 ? '' : `gh: HTTP ${status}\n` });

// The shared fake plus PRs, checks, label adds, comment deletes, issue close and the pr merge command.
function extend(f, w) {
  f.prs = new Map(); f.checks = new Map(); f.statuses = new Map(); f.merges = []; f.writes = [];
  const prefix = `repos/${f.repo}`;
  const restPr = pr => ({ number: pr.number, state: pr.state, merged: pr.merged, body: pr.body, title: pr.title, html_url: `https://github.com/${f.repo}/pull/${pr.number}`,
    head: { sha: pr.head, ref: pr.branch, repo: { full_name: f.repo } }, base: { ref: pr.base, repo: { full_name: f.repo } }, merge_commit_sha: pr.mergeSha ?? null, draft: Boolean(pr.draft) });
  f.openPr = ({ branch, head, body = 'Fixes the issue.\n\nRuntime: PASS\nPath: d — change.txt — unowned — no contract change — Test: done check', base = 'main', title = 'Change' }) => {
    const pr = { number: 100 + f.prs.size, branch, head, base, body, title, state: 'open', merged: false, comments: [], labels: [] };
    f.prs.set(pr.number, pr); return pr;
  };
  f.listCatchUp = () => { for (const pr of f.prs.values()) if (pr.hidden) pr.hidden['pdd:merge-lane'] = 0; };
  f.setChecks = (sha, conclusion = 'success', status = 'completed') => f.checks.set(sha, [{ name: 'ci', status, conclusion: status === 'completed' ? conclusion : null }]);
  // Check runs with an id and an app (#3181): setRun puts the latest run of a name. With f.rerunnable (off by default)
  // the rerun endpoints answer 201 and put a new queued run of that name; off, they answer 404 like an unknown route.
  f.nextRun = 7000; f.rerunnable = false; f.reruns = [];
  f.setRun = (sha, { name = 'ci', status = 'completed', conclusion = 'success', app = 'github-actions' } = {}) => {
    const run = { id: f.nextRun++, name, status, conclusion: status === 'completed' ? conclusion : null, app: { slug: app } };
    f.checks.set(sha, [...(f.checks.get(sha) ?? []).filter(r => r.name !== name), run]); return run;
  };
  const original = f.gh;
  f.gh = async (args, options = {}) => {
    if (args[0] === 'pr' && args[1] === 'merge') {
      f.writes.push(['merge', ...args]);
      const pr = f.prs.get(Number(args[2])), head = args[args.indexOf('--match-head-commit') + 1];
      if (!pr || pr.state !== 'open') return { code: 1, stdout: '', stderr: 'not open' };
      if (head !== pr.head) return { code: 1, stdout: '', stderr: 'head changed' };
      if (!args.includes('--merge')) return { code: 1, stdout: '', stderr: 'merge method' };
      pr.state = 'closed'; pr.merged = true; pr.mergeSha = 'f'.repeat(40); f.merges.push(pr.number);
      // With mergeMovesBase, the merge lands on the remote main like on GitHub (a merge commit of the PR head).
      if (f.mergeMovesBase) {
        const seed = join(w.dir, `merge-${pr.number}`); git(w.dir, 'clone', '-q', w.remote, seed);
        git(seed, 'fetch', '-q', 'origin', pr.branch); git(seed, 'merge', '-q', '--no-ff', '-m', `Merge PR #${pr.number}`, 'FETCH_HEAD'); git(seed, 'push', '-q', 'origin', 'HEAD:main');
        pr.mergeSha = git(seed, 'rev-parse', 'HEAD');
      }
      return { code: 0, stdout: '', stderr: '' };
    }
    if (args[0] === 'pr' && args[1] === 'ready') {
      f.writes.push(['ready', ...args]);
      const pr = f.prs.get(Number(args[2])); if (!pr || pr.state !== 'open') return { code: 1, stdout: '', stderr: 'not open' };
      pr.draft = args.includes('--undo'); return { code: 0, stdout: '', stderr: '' };
    }
    if (args[0] !== 'api') return original(args, options);
    if (args[4] === 'user' && methodOf(args) === 'GET') return ok(200, { login: f.owner });
    const endpoint = endpointOf(args) ?? '', method = methodOf(args), input = options.input ? JSON.parse(options.input) : undefined;
    if (!endpoint.startsWith(prefix)) return original(args, options);
    const route = endpoint.slice(prefix.length).split('?')[0];
    if (method !== 'GET') f.writes.push([method, route, input]);
    let m;
    if ((m = /^\/compare\/([^/]+)\.\.\.([0-9a-f]{40})$/.exec(route))) {
      const count = range => Number(spawnSync('git', ['--git-dir', w.remote, 'rev-list', '--count', range], { encoding: 'utf8' }).stdout.trim());
      const base = decodeURIComponent(m[1]), behind = count(`${m[2]}..refs/heads/${base}`), ahead = count(`refs/heads/${base}..${m[2]}`);
      return ok(200, { behind_by: behind, ahead_by: ahead, status: behind ? (ahead ? 'diverged' : 'behind') : ahead ? 'ahead' : 'identical' });
    }
    if (route === '/pulls' && method === 'GET') {
      const params = new URLSearchParams(endpoint.split('?')[1] ?? ''), head = params.get('head')?.split(':').pop(), state = params.get('state') ?? 'open';
      return ok(200, [...f.prs.values()].filter(pr => (state === 'all' || pr.state === state) && (!head || pr.branch === head)).map(restPr));
    }
    if ((m = /^\/pulls\/(\d+)$/.exec(route))) {
      const pr = f.prs.get(Number(m[1])); if (!pr) return ok(404, { message: 'Not Found' });
      const tip = spawnSync('git', ['--git-dir', w.remote, 'rev-parse', '--verify', '-q', `refs/heads/${pr.branch}`], { encoding: 'utf8' }).stdout.trim();
      if (/^[0-9a-f]{40}$/.test(tip) && tip !== pr.syncedTip) { pr.head = tip; pr.syncedTip = tip; }
      if (method === 'PATCH') { if (input.body !== undefined) pr.body = input.body; if (input.state) pr.state = input.state; }
      return ok(200, restPr(pr));
    }
    // Labels on PRs (the merge lane) and the open issues-and-PRs list for one label.
    if ((m = /^\/issues\/(\d+)\/labels(?:\/(.+))?$/.exec(route)) && f.prs.has(Number(m[1]))) {
      const pr = f.prs.get(Number(m[1]));
      if (method === 'POST') { for (const name of input.labels) if (!pr.labels.includes(name)) { pr.labels.push(name); (pr.hidden ??= {})[name] = f.labelListLag ?? 0; } return ok(200, pr.labels.map(name => ({ name }))); }
      if (method === 'DELETE') { const name = decodeURIComponent(m[2] ?? ''); if (!pr.labels.includes(name)) return ok(404, { message: 'Label does not exist' }); pr.labels = pr.labels.filter(x => x !== name); return ok(200, []); }
    }
    // A PR's own issue read is consistent: it shows a label at once.
    if ((m = /^\/issues\/(\d+)$/.exec(route)) && method === 'GET' && f.prs.has(Number(m[1])) && !f.issues.has(Number(m[1]))) { const pr = f.prs.get(Number(m[1])); return ok(200, { number: pr.number, state: pr.state, labels: pr.labels.map(name => ({ name })), pull_request: {} }); }
    // With labelListLag K (off by default), the label list misses a label that a POST added for the next K list reads
    // (the reads of every machine count), as GitHub's list can lag a write. listCatchUp() ends every lag at once.
    if (route === '/issues' && method === 'GET' && new URLSearchParams(endpoint.split('?')[1] ?? '').get('labels') === 'pdd:merge-lane') {
      const rows = [...f.prs.values()].filter(pr => pr.state === 'open' && pr.labels.includes('pdd:merge-lane') && !(pr.hidden?.['pdd:merge-lane'] > 0));
      for (const pr of f.prs.values()) if (pr.hidden?.['pdd:merge-lane'] > 0) pr.hidden['pdd:merge-lane']--;
      return ok(200, rows.map(pr => ({ number: pr.number, state: 'open', labels: pr.labels.map(name => ({ name })), pull_request: {} })));
    }
    // PR reviews on GitHub (a person's APPROVED review).
    if ((m = /^\/pulls\/(\d+)\/reviews$/.exec(route)) && method === 'GET') return ok(200, f.prs.get(Number(m[1]))?.reviews ?? []);
    if ((m = /^\/issues\/(\d+)\/comments$/.exec(route)) && f.prs.has(Number(m[1]))) {
      const pr = f.prs.get(Number(m[1]));
      if (method === 'POST') { const c = { id: f.nextComment++, body: input.body, user: { login: f.owner } }; pr.comments.push(c); return ok(201, c); }
      return ok(200, pr.comments);
    }
    if (f.rerunnable && method === 'POST' && (m = /^\/(?:actions\/jobs\/(\d+)\/rerun|check-runs\/(\d+)\/rerequest)$/.exec(route))) {
      const id = Number(m[1] ?? m[2]), sha = [...f.checks.keys()].find(key => f.checks.get(key).some(r => r.id === id));
      if (!sha) return ok(404, { message: 'Not Found' });
      const old = f.checks.get(sha).find(r => r.id === id);
      f.reruns.push({ id, sha, name: old.name, route }); f.setRun(sha, { name: old.name, status: 'queued', app: old.app?.slug });
      return ok(201, {});
    }
    if ((m = /^\/commits\/([0-9a-f]{40})\/check-runs$/.exec(route))) { const runs = f.checks.get(m[1]) ?? []; return ok(200, { total_count: runs.length, check_runs: runs }); }
    if ((m = /^\/commits\/([0-9a-f]{40})\/status$/.exec(route))) { const statuses = f.statuses.get(m[1]) ?? []; return ok(200, { state: statuses.length ? statuses.every(s => s.state === 'success') ? 'success' : 'failure' : 'pending', statuses }); }
    if ((m = /^\/issues\/(\d+)\/labels$/.exec(route)) && method === 'POST') {
      const issue = f.issues.get(Number(m[1])); if (!issue) return ok(404, { message: 'Not Found' });
      for (const name of input.labels) if (!issue.labels.includes(name)) f.label(issue.number, name);
      return ok(200, issue.labels.map(name => ({ name })));
    }
    if ((m = /^\/issues\/comments\/(\d+)$/.exec(route)) && method === 'DELETE') {
      for (const issue of f.issues.values()) { const i = issue.comments.findIndex(c => c.id === m[1]); if (i >= 0) { issue.comments.splice(i, 1); return { code: 0, stdout: 'HTTP/2.0 204 No Content\r\n\r\n', stderr: '' }; } }
      return ok(404, { message: 'Not Found' });
    }
    if ((m = /^\/issues\/(\d+)$/.exec(route)) && method === 'PATCH') {
      const issue = f.issues.get(Number(m[1])); if (!issue) return ok(404, { message: 'Not Found' });
      if (input.state === 'closed') f.close(issue.number);
      if (input.body !== undefined) f.edit(issue.number, input.body);
      return ok(200, { number: issue.number, state: issue.state });
    }
    if (route === '/issues' && method === 'POST') {
      const n = Math.max(0, ...f.issues.keys()) + 1;
      const issue = f.add(n, { title: input.title, body: input.body, labels: input.labels ?? [], assignees: input.assignees ?? [], user: f.owner, created: f.now(), updated: f.now() });
      return ok(201, { id: Number(issue.id), number: n, html_url: `https://github.com/${f.repo}/issues/${n}`, title: issue.title });
    }
    if (route === '' && method === 'GET') return ok(200, { full_name: f.repo, owner: { login: f.owner }, default_branch: 'main' });
    return original(args, options);
  };
  return f;
}

const git = (cwd, ...args) => execFileSync('git', args, { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], env: { ...process.env, GIT_AUTHOR_NAME: 't', GIT_AUTHOR_EMAIL: 't@x', GIT_COMMITTER_NAME: 't', GIT_COMMITTER_EMAIL: 't@x' } }).trim();

export async function coreWorld(t, { repository = 'acme/widgets', settings = {}, machine = 'machine-a', coordinatorId = 'coord-a', shared } = {}) {
  const dir = shared?.dir ?? mkdtempSync(join(tmpdir(), 'pdd-core-world-'));
  if (!shared) t.after(() => rmSync(dir, { recursive: true, force: true }));
  const w = { dir, time: shared?.time ?? Date.parse('2026-11-10T12:00:00Z'), started: [], alive: new Set(), stopped: [], ticks: [] };
  w.clock = shared?.clock ?? { now: () => w.clock.at, at: w.time };
  w.now = () => w.clock.at;
  w.advance = ms => { w.clock.at += ms; };
  if (shared) { Object.assign(w, { remote: shared.remote, github: shared.github, reports: shared.reports }); }
  else {
    w.remote = join(dir, 'origin.git');
    git(dir, 'init', '-q', '--bare', '-b', 'main', w.remote);
    const seed = join(dir, 'seed'); git(dir, 'clone', '-q', w.remote, seed);
    writeFileSync(join(seed, 'README.md'), 'value 1\n'); git(seed, 'add', '.'); git(seed, 'commit', '-qm', 'seed'); git(seed, 'push', '-q', 'origin', 'HEAD:main');
    w.github = extend(createGithubRepoFake({ repository, owner: 'acme', issues: 0, now: w.now }), w);
    w.reports = extend(createGithubRepoFake({ repository: 'promptdriven/pdd', owner: 'promptdriven', issues: 0, now: w.now }), w);
  }
  w.cwd = join(dir, `clone-${machine}`); git(dir, 'clone', '-q', w.remote, w.cwd);
  w.state = { cwd: w.cwd, repo: repository, coordinatorId, machine, baseBranch: 'main', agent: { kind: 'codex', command: 'codex' },
    packageRoot: join(dir, 'pkg'), stateFile: join(dir, `state-${machine}.json`) };
  w.root = join(dir, `core-${machine}`); w.reportRoot = join(dir, `reports-${machine}`);
  // Tests keep reports as local drafts unless they ask for another mode (the product default is draft too).
  w.settings = coreSettings({ autopilot: { mode: 'auto', engine: 'core', testCommand: 'npm test', report: 'draft', ...settings } });
  w.gh = async (args, options) => {
    const endpoint = endpointOf(args) ?? '';
    return endpoint.startsWith('repos/promptdriven/pdd') && repository.toLowerCase() !== 'promptdriven/pdd' ? w.reports.gh(args, options) : w.github.gh(args, options);
  };
  // The scripted agent job runner. A job is alive until the test finishes it.
  let pid = 1000 + (machine === 'machine-a' ? 0 : 5000);
  w.jobs = {
    start: spec => {
      const job = { ...spec, pid: ++pid, token: `${spec.dir}/${spec.id}.spec.json`, log: join(spec.dir, `${spec.id}.log`), exit: join(spec.dir, `${spec.id}.exit.json`),
        result: join(spec.dir, `${spec.id}.result.json`), started: w.now() };
      // A suite starts admitted by the machine's suite queue, unless the test queues it (w.suiteQueued, then w.admit).
      writeFileSync(job.log, ['suite', 'vectors'].includes(spec.role) ? (w.suiteQueued ? 'waiting for a check slot (position 1)\n' : 'running the full test suite\n') : `log of ${spec.id}\nError: pdd test returned no verdict\n`);
      w.started.push(job); w.alive.add(job.pid); return job;
    },
    read: job => ({ state: w.alive.has(job.pid) ? 'running' : existsSync(job.exit) ? 'exited' : 'dead',
      exit: existsSync(job.exit) ? JSON.parse(readFileSync(job.exit, 'utf8')) : null,
      result: existsSync(job.result) ? JSON.parse(readFileSync(job.result, 'utf8')) : null,
      log: existsSync(job.log) ? { size: statSync(job.log).size, mtime: statSync(job.log).mtimeMs } : null }),
    stop: job => { const was = w.alive.delete(job.pid); if (was) w.stopped.push(job.id); return was; },
    // CPU seconds by child pid, as agentJobCpu gives them; null when the test sets none.
    cpu: job => w.cpu.get(job.pid) ?? null,
  };
  w.cpu = new Map();
  w.job = (issue, role) => [...w.started].reverse().find(j => j.issue === issue && (!role || j.role === role));
  // Finish a job: exit record, optional result file.
  w.finish = (issue, role, { code = 0, result } = {}) => {
    const job = w.job(issue, role); if (!job) throw Error(`no ${role} job for #${issue}`);
    w.alive.delete(job.pid);
    if (result) writeFileSync(job.result, JSON.stringify(result));
    writeFileSync(job.exit, JSON.stringify({ code, signal: null, at: w.now() }));
    return job;
  };
  // The agent makes progress: one new item in its stream (a tool call for an agent, a new test line for the suite).
  // The words are new each time; numbers alone are not new (they are normalized away).
  let steps = 0;
  const word = n => { let text = ''; do { text = String.fromCharCode(97 + n % 26) + text; n = Math.floor(n / 26); } while (n > 0); return text; };
  w.line = (role, text) => role === 'suite' ? `${text}\n` : `${JSON.stringify({ type: 'assistant', message: { content: [{ type: 'tool_use', name: 'Bash', input: { command: text } }] } })}\n`;
  w.step = job => appendFileSync(job.log, w.line(job.role, `ok step ${word(steps++)}`));
  w.progress = (issue, role) => w.step(w.job(issue, role));
  w.admit = issue => appendFileSync(w.job(issue, 'suite').log, 'running the full test suite\n');
  w.say = (issue, role, text) => appendFileSync(w.job(issue, role).log, text.endsWith('\n') ? text : `${text}\n`);
  w.kill = (issue, role) => { const job = w.job(issue, role); w.alive.delete(job.pid); return job; };
  // The scripted builder: commit on the job branch, push, open a PR, finish with a pr result.
  // A scripted PR body gets a debate-A Path line unless it has one or the test asks for none (pathLine: false).
  // write: false commits only what the test put in the worktree (a conflict fix), not the change-N.txt file.
  // add: false commits only what the test staged (the rest of the worktree stays as it is, for example not committed).
  w.build = (issue, { body, role = 'build', checks = 'success', runtime, result = {}, pathLine = true, write = true, add = true } = {}) => {
    const job = w.job(issue, role);
    if (body && pathLine && !/^[\s>*-]*Path:/m.test(body)) body = `${body}\nPath: d — change-${issue}.txt — unowned — no contract change — Test: done check`;
    if (write) writeFileSync(join(job.cwd, `change-${issue}.txt`), `change ${job.id}\n`);
    if (add) git(job.cwd, 'add', '.');
    if (git(job.cwd, 'diff', '--cached', '--name-only')) git(job.cwd, 'commit', '-qm', `change ${job.id}`); git(job.cwd, 'push', '-q', 'origin', `HEAD:${job.branch}`);
    const head = git(job.cwd, 'rev-parse', 'HEAD');
    let pr = [...w.github.prs.values()].find(p => p.branch === job.branch);
    if (pr) { pr.head = head; if (body) pr.body = body; } else pr = w.github.openPr({ branch: job.branch, head, ...(body ? { body } : {}) });
    pr.syncedTip = head;
    if (checks) w.github.setChecks(head, checks);
    w.finish(issue, role, { result: { outcome: 'pr', pr: pr.number, head, ...(runtime ? { runtime } : {}), ...result } });
    return { pr, head };
  };
  w.review = (issue, verdict, mustFix = []) => {
    const job = w.job(issue, 'review');
    w.finish(issue, 'review', { result: { verdict, head: job.head, summary: `Review ${verdict}`, mustFix } });
  };
  w.suite = (issue, code = 0) => w.finish(issue, 'suite', { code });
  // The engine's replay and formal run (T04): each file runs alone and prints its TAP summary and then its marker line
  // with the run's nonce. w.replayFiles lists [kind, index] from the command; w.tapFile writes one file's part.
  w.replayFiles = job => [...(job.args.at(-3) ?? '').matchAll(/# pdd-autopilot-([0-9a-f]+): ([a-z-]+) (\d+) exit/g)].map(m => ({ nonce: m[1], kind: m[2], index: Number(m[3]) }));
  w.tapFile = (job, kind, index, { tests = 1, fail = 0, failed = [], skipped = 0, code } = {}) => {
    const nonce = w.replayFiles(job)[0]?.nonce ?? 'none';
    return [...failed.map((f, i) => `not ok ${i + 1} - ${f.name}\n  ---\n  location: '${job.cwd}/${f.file}:1:1'\n  ...`),
      `1..${tests}`, `# tests ${tests}`, `# pass ${tests - fail - skipped}`, `# fail ${fail}`, `# skipped ${skipped}`, `# pdd-autopilot-${nonce}: ${kind} ${index} exit ${code ?? (fail ? 1 : 0)}`, ''].join('\n');
  };
  // The whole run: `tests`, `fail` and `failed` go to the first file of the kind (other files pass 1 test each, so the
  // kind's total is `tests`); `formal` gives the formal part; `code` sets the first file's exit. `linked` (replay files
  // that import a changed module) and `control` (each control kind) pass 1 test per file unless given.
  w.vectorsRun = (issue, { formal, linked, control, ...vectors } = {}) => {
    const job = w.job(issue, 'vectors'), files = w.replayFiles(job), parts = [], used = [];
    const hasVectors = files.some(f => f.kind === 'vectors'), formalPart = formal ?? (hasVectors ? { tests: 1 } : vectors);
    for (const kind of ['vectors', 'formal', 'linked', 'control-vectors', 'control-formal']) {
      const mine = files.filter(f => f.kind === kind);
      const whole = kind === 'vectors' ? vectors : kind === 'formal' ? formalPart : kind === 'linked' ? linked ?? { tests: mine.length } : control?.[kind] ?? { tests: mine.length };
      if (!mine.length) continue;
      used.push(whole);
      const total = whole.tests ?? 3, rest = mine.length - 1;
      mine.forEach((f, i) => parts.push(w.tapFile(job, kind, f.index, i === 0 ? { ...whole, tests: Math.max(1, total - rest) } : { tests: 1 })));
    }
    appendFileSync(job.log, parts.join(''));
    return w.finish(issue, 'vectors', { code: used.some(k => k.fail || k.code) ? 1 : 0 });
  };
  w.issue = (n, extra = {}) => w.github.add(n, { created: w.now() - (1000 - n) * 60000, updated: w.now() - 60000, ...extra });
  w.ports = (extra = {}) => ({
    gh: w.gh,
    git: async (args, { cwd } = {}) => { const r = spawnSync('git', args, { cwd: cwd ?? w.cwd, encoding: 'utf8' }); return { code: r.status, stdout: r.stdout, stderr: r.stderr }; },
    now: w.now, root: w.root, reportRoot: w.reportRoot, jobs: w.jobs, version: '0.1.27',
    listIssues: async () => { const r = await w.gh(['api', '--include', '--method', 'GET', `repos/${repository.toLowerCase()}/issues?state=open&per_page=100`]); return JSON.parse(r.stdout.split(/\r?\n\r?\n/).slice(1).join('\n\n')); },
    trusted: async row => ['acme', 'promptdriven'].includes(row.user?.login),
    checkBase: async () => ({ exitCode: 0, message: 'Base check ok.' }),
    // The saved Runtime checks (T01). By default every changed Story and prompt is covered at the head; a test of the
    // coverage rule sets w.runtimeEvidence.
    runtimeEvidence: async (input, ctx) => {
      w.evidenceReads = [...(w.evidenceReads ?? []), input];
      if (w.runtimeEvidence) return w.runtimeEvidence(input, ctx);
      const changed = spawnSync('git', ['diff', '--name-only', 'origin/main...HEAD'], { cwd: input.tree, encoding: 'utf8' }).stdout.split('\n').filter(Boolean);
      const stories = changed.filter(file => /^user_stories\/.+\.md$/.test(file));
      return { stories: [{ story: 'user_stories/all.md', pass: true, current: true }, ...stories.map(story => ({ story, pass: true, current: true }))], storyFiles: stories,
        footprints: { 'user_stories/all.md': changed.filter(file => file.endsWith('.prompt.md')) } };
    },
    agentReady: async () => true,
    warn: () => {},
    ...extra,
  });
  w.tick = async (extra = {}) => { const r = await tickCore({ state: w.state, settings: w.settings, budget: { state: 'normal' } }, w.ports(extra)); w.ticks.push(r); return r; };
  w.peer = async (options = {}) => coreWorld(t, { repository, settings, machine: 'machine-b', coordinatorId: 'coord-b', ...options,
    shared: { dir, remote: w.remote, github: w.github, reports: w.reports, clock: w.clock } });
  w.comments = n => w.github.issues.get(n).comments.map(c => c.body);
  w.baseCommit = (file, text) => {
    const seed = join(dir, `seed-${Math.random().toString(36).slice(2)}`); git(dir, 'clone', '-q', w.remote, seed);
    mkdirSync(dirname(join(seed, file)), { recursive: true }); writeFileSync(join(seed, file), text); git(seed, 'add', '.'); git(seed, 'commit', '-qm', `base ${file}`); git(seed, 'push', '-q', 'origin', 'HEAD:main');
    return git(seed, 'rev-parse', 'HEAD');
  };
  w.labels = n => w.github.issues.get(n).labels;
  w.git = git;
  return w;
}
