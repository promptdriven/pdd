// Synthetic day. Use the repo's fake GitHub and real heartbeat implementation.
// baseline=true keeps the previous three separate label requests and append-only
// progress comments; the previous heartbeat source can be selected with src.
import { mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { createGithubRepoFake } from './github-repo-fake.mjs';

export async function replayWriteDay({ src = new URL('../../src/', import.meta.url).pathname, baseline = false } = {}) {
  const { refreshClaimHeartbeat } = await import(pathToFileURL(join(src, 'issue-dependencies-github.mjs')));
  const { githubWriteRunner } = baseline ? {} : await import(pathToFileURL(join(src, 'github-write-proxy.mjs')));
  const root = mkdtempSync(join(tmpdir(), 'pdd-write-day-'));
  let time = Date.parse('2026-11-07T00:00:00Z');
  const fake = createGithubRepoFake({ repository: 'acme/widgets', issues: 8, now: () => time });
  const exec = (_file, args, options) => fake.gh(args, options);
  const run = baseline ? exec : githubWriteRunner(exec, { root, env: {}, identity: 'acme', machine: 'one', now: () => time });
  const claims = [];
  for (let n = 1; n <= 8; n++) {
    fake.label(n, 'phase:a');
    const comment = fake.claim(n, { coordinatorId: 'a', machine: 'one' });
    claims.push({ issue: `https://github.com/acme/widgets/issues/${n}`, active: true, coordinatorId: 'a', machine: 'one', commentId: comment.id,
      labelEventId: fake.issues.get(n).timeline.at(-1).id, lastSeen: new Date(time).toISOString() });
  }
  const api = (method, path, body) => run('gh', ['api', '--include', '--method', method, path, ...(body ? ['--input', '-'] : [])], body ? { input: JSON.stringify(body) } : {});
  try {
    for (let tick = 1; tick <= 48; tick++) {
      time += 30 * 60_000;
      for (let i = 0; i < claims.length; i++) {
        const n = i + 1, claim = claims[i], path = `repos/acme/widgets/issues/${n}`;
        const beat = await refreshClaimHeartbeat({ repository: 'acme/widgets', claim, coordinatorId: 'a', machine: 'one', at: new Date(time).toISOString() }, { execFile: run });
        if (beat.state === 'refreshed') claim.lastSeen = beat.lastSeen;
        const stage = Math.floor((tick - 1) / 4), next = stage % 2 ? 'a' : 'b', old = next === 'a' ? 'b' : 'a';
        await api('POST', `${path}/comments`, { body: `Progress ${stage}\n\n<!-- pdd:autopilot:status -->` });
        if ((tick - 1) % 4 === 0) {
          if (baseline) {
            await api('POST', `${path}/labels`, { labels: [`phase:${next}`] });
            await api('DELETE', `${path}/labels/phase%3A${old}`);
            await api('POST', `${path}/labels`, { labels: ['pdd:tracked'] });
          } else await run('gh', ['issue', 'edit', String(n), '--repo', 'acme/widgets', '--add-label', `phase:${next},pdd:tracked`, '--remove-label', `phase:${old}`]);
        }
      }
    }
    const calls = fake.calls.filter(c => c.method !== 'GET');
    const claimIds=new Set(claims.map(c=>c.commentId));
    const heartbeatWrites=calls.filter(c=>c.method==='PATCH' && claimIds.has(c.endpoint.split('/').at(-1))).length;
    const statusWrites=calls.filter(c=>c.method==='POST' && c.endpoint.endsWith('/comments') || c.method==='PATCH' && c.endpoint.includes('/issues/comments/') && !claimIds.has(c.endpoint.split('/').at(-1))).length;
    return { heartbeatWrites,statusWrites,writes: calls.length,
      postComments: calls.filter(c => c.method === 'POST' && c.endpoint.endsWith('/comments')).length,
      labelWrites: calls.filter(c => c.endpoint.includes('/labels') || c.endpoint === 'graphql' && c.query?.startsWith('mutation')).length,
      comments: [...fake.issues.values()].reduce((sum, issue) => sum + issue.comments.length, 0),
      final: [...fake.issues.values()].map(issue => ({ number: issue.number, labels: issue.labels.slice().sort(), progress: issue.comments.filter(c => c.body.includes('pdd:autopilot:status')).at(-1).body })) };
  } finally { rmSync(root, { recursive: true, force: true }); }
}
