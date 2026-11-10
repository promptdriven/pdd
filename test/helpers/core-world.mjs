// A small offline world for the Autopilot core tick: a fake GitHub (one work repository and the
// promptdriven/pdd report repository), a real local Git origin and clone, a fake clock and a scripted
// agent job runner. No network, no real agent, no timer.
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
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
    head: { sha: pr.head, ref: pr.branch, repo: { full_name: f.repo } }, base: { ref: pr.base, repo: { full_name: f.repo } }, merge_commit_sha: pr.mergeSha ?? null });
  f.openPr = ({ branch, head, body = 'Fixes the issue.\n\nRuntime: PASS', base = 'main', title = 'Change' }) => {
    const pr = { number: 100 + f.prs.size, branch, head, base, body, title, state: 'open', merged: false, comments: [] };
    f.prs.set(pr.number, pr); return pr;
  };
  f.setChecks = (sha, conclusion = 'success', status = 'completed') => f.checks.set(sha, [{ name: 'ci', status, conclusion: status === 'completed' ? conclusion : null }]);
  const original = f.gh;
  f.gh = async (args, options = {}) => {
    if (args[0] === 'pr' && args[1] === 'merge') {
      f.writes.push(['merge', ...args]);
      const pr = f.prs.get(Number(args[2])), head = args[args.indexOf('--match-head-commit') + 1];
      if (!pr || pr.state !== 'open') return { code: 1, stdout: '', stderr: 'not open' };
      if (head !== pr.head) return { code: 1, stdout: '', stderr: 'head changed' };
      if (!args.includes('--merge')) return { code: 1, stdout: '', stderr: 'merge method' };
      pr.state = 'closed'; pr.merged = true; pr.mergeSha = 'f'.repeat(40); f.merges.push(pr.number);
      return { code: 0, stdout: '', stderr: '' };
    }
    if (args[0] === 'pr' && args[1] === 'ready') {
      f.writes.push(['ready', ...args]);
      const pr = f.prs.get(Number(args[2])); if (!pr || pr.state !== 'open') return { code: 1, stdout: '', stderr: 'not open' };
      pr.draft = args.includes('--undo'); return { code: 0, stdout: '', stderr: '' };
    }
    if (args[0] !== 'api') return original(args, options);
    const endpoint = endpointOf(args) ?? '', method = methodOf(args), input = options.input ? JSON.parse(options.input) : undefined;
    if (!endpoint.startsWith(prefix)) return original(args, options);
    const route = endpoint.slice(prefix.length).split('?')[0];
    if (method !== 'GET') f.writes.push([method, route, input]);
    let m;
    if ((m = /^\/pulls\/(\d+)$/.exec(route))) {
      const pr = f.prs.get(Number(m[1])); if (!pr) return ok(404, { message: 'Not Found' });
      if (method === 'PATCH') { if (input.body !== undefined) pr.body = input.body; if (input.state) pr.state = input.state; }
      return ok(200, restPr(pr));
    }
    if ((m = /^\/issues\/(\d+)\/comments$/.exec(route)) && f.prs.has(Number(m[1]))) {
      const pr = f.prs.get(Number(m[1]));
      if (method === 'POST') { const c = { id: f.nextComment++, body: input.body, user: { login: f.owner } }; pr.comments.push(c); return ok(201, c); }
      return ok(200, pr.comments);
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
  w.settings = coreSettings({ autopilot: { mode: 'auto', engine: 'core', testCommand: 'npm test', ...settings } });
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
      writeFileSync(job.log, `log of ${spec.id}\nError: pdd test returned no verdict\n`);
      w.started.push(job); w.alive.add(job.pid); return job;
    },
    read: job => ({ state: w.alive.has(job.pid) ? 'running' : existsSync(job.exit) ? 'exited' : 'dead',
      exit: existsSync(job.exit) ? JSON.parse(readFileSync(job.exit, 'utf8')) : null,
      result: existsSync(job.result) ? JSON.parse(readFileSync(job.result, 'utf8')) : null }),
    stop: job => { const was = w.alive.delete(job.pid); if (was) w.stopped.push(job.id); return was; },
  };
  w.job = (issue, role) => [...w.started].reverse().find(j => j.issue === issue && (!role || j.role === role));
  // Finish a job: exit record, optional result file.
  w.finish = (issue, role, { code = 0, result } = {}) => {
    const job = w.job(issue, role); if (!job) throw Error(`no ${role} job for #${issue}`);
    w.alive.delete(job.pid);
    if (result) writeFileSync(job.result, JSON.stringify(result));
    writeFileSync(job.exit, JSON.stringify({ code, signal: null, at: w.now() }));
    return job;
  };
  w.kill = (issue, role) => { const job = w.job(issue, role); w.alive.delete(job.pid); return job; };
  // The scripted builder: commit on the job branch, push, open a PR, finish with a pr result.
  w.build = (issue, { body, role = 'build', checks = 'success', runtime } = {}) => {
    const job = w.job(issue, role);
    writeFileSync(join(job.cwd, `change-${issue}.txt`), `change ${job.id}\n`);
    git(job.cwd, 'add', '.'); git(job.cwd, 'commit', '-qm', `change ${job.id}`); git(job.cwd, 'push', '-q', 'origin', `HEAD:${job.branch}`);
    const head = git(job.cwd, 'rev-parse', 'HEAD');
    let pr = [...w.github.prs.values()].find(p => p.branch === job.branch);
    if (pr) { pr.head = head; if (body) pr.body = body; } else pr = w.github.openPr({ branch: job.branch, head, ...(body ? { body } : {}) });
    if (checks) w.github.setChecks(head, checks);
    w.finish(issue, role, { result: { outcome: 'pr', pr: pr.number, head, ...(runtime ? { runtime } : {}) } });
    return { pr, head };
  };
  w.review = (issue, verdict, mustFix = []) => {
    const job = w.job(issue, 'review');
    w.finish(issue, 'review', { result: { verdict, head: job.head, summary: `Review ${verdict}`, mustFix } });
  };
  w.suite = (issue, code = 0) => w.finish(issue, 'suite', { code });
  w.issue = (n, extra = {}) => w.github.add(n, { created: w.now() - (1000 - n) * 60000, updated: w.now() - 60000, ...extra });
  w.ports = (extra = {}) => ({
    gh: w.gh,
    git: async (args, { cwd } = {}) => { const r = spawnSync('git', args, { cwd: cwd ?? w.cwd, encoding: 'utf8' }); return { code: r.status, stdout: r.stdout, stderr: r.stderr }; },
    now: w.now, root: w.root, reportRoot: w.reportRoot, jobs: w.jobs, version: '0.1.27',
    listIssues: async () => { const r = await w.gh(['api', '--include', '--method', 'GET', `repos/${repository.toLowerCase()}/issues?state=open&per_page=100`]); return JSON.parse(r.stdout.split(/\r?\n\r?\n/).slice(1).join('\n\n')); },
    trusted: async row => ['acme', 'promptdriven'].includes(row.user?.login),
    checkBase: async () => ({ exitCode: 0, message: 'Base check ok.' }),
    agentReady: async () => true,
    warn: () => {},
    ...extra,
  });
  w.tick = async (extra = {}) => { const r = await tickCore({ state: w.state, settings: w.settings, budget: { state: 'normal' } }, w.ports(extra)); w.ticks.push(r); return r; };
  w.peer = async (options = {}) => coreWorld(t, { repository, settings, machine: 'machine-b', coordinatorId: 'coord-b', ...options,
    shared: { dir, remote: w.remote, github: w.github, reports: w.reports, clock: w.clock } });
  w.comments = n => w.github.issues.get(n).comments.map(c => c.body);
  w.labels = n => w.github.issues.get(n).labels;
  w.git = git;
  return w;
}
