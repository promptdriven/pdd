// Generated from prompts/cli/workflow-github.prompt.md (sha256: cc5e47d00f72396a5e40f732e7782e48599a8310b13b5d65225bc33299196442).
import { execFile } from 'node:child_process';
import { isAbsolute } from 'node:path';
import { runtimeOutputSlice, causeText } from './runtime-seam.mjs';
import { nativeGithubCounter } from './github-calls.mjs';

runtimeOutputSlice();

const execute = (file, args, options) => new Promise((resolve, reject) => {
  const { input, ...execOptions } = options;
  const child = execFile(file, args, execOptions, (error, stdout, stderr) => {
    if (error) { error.stdout = stdout; error.stderr = stderr; reject(error); }
    else resolve({ stdout, stderr });
  });
  if (input !== undefined) { child.stdin.on('error', () => {}); child.stdin.end(input); }
});
const fields = 'number,url,state,headRefName,baseRefName,headRefOid,mergeCommit,body,isCrossRepository,headRepository,headRepositoryOwner,isDraft';
const identifier = value => typeof value === 'string' && /^[A-Za-z0-9][A-Za-z0-9_.-]{0,159}$/.test(value);
const text = value => typeof value === 'string' && value.length > 0 && !/[\u0000-\u001f\u007f]/u.test(value);
const repositoryName = value => text(value) && /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/.test(value);
const sha = value => typeof value === 'string' && /^[a-f0-9]{40}$/.test(value);
export const sameRepo = (a, b) => typeof a === 'string' && typeof b === 'string' && a.toLowerCase() === b.toLowerCase();
const fail = code => { throw Object.assign(new Error(code), { code }); };
const parseJson = value => { try { return JSON.parse(value); } catch { fail('workflow_github_json_invalid'); } };
const outcome = (state, message, pr = null) => ({ state, pr, message });
// GitHub refuses a PR description over 65,536 characters, counted as Unicode code points (0.1.7 tester: 105,489).
const PR_BODY_LIMIT = 65_536, characters = value => [...value].length;
const prCause = value => {
  const hidden = String(value ?? '')
    .replace(/(["'])(?:file:\/\/|[A-Za-z]:[\\/]|\\\\|\/)[^\r\n]*?\1/gi, '<local path>')
    .replace(/\bfile:\/\/[^\s"'<>)]*/gi, '<local path>')
    .replace(/(?:\b[A-Za-z]:[\\/]|\\\\[^\\/\s]+[\\/])[^\s"'<>)]*/g, '<local path>')
    .replace(/(?<![\w.:/\\-])\/(?!\/)[^\s"'<>)]*/g, '<local path>');
  return causeText(hidden);
};
// gh's error line, cleaned of tokens: gh may print "Creating pull request for …" first.
const ghLine = stderr => { const lines = String(stderr).split(/\r?\n/).map(line => prCause(line)).filter(Boolean);
  return lines.find(line => /GraphQL:|error|fail|HTTP \d{3}|denied|refused|not found/i.test(line)) ?? lines.at(-1) ?? ''; };
// GitHub's own refusal of the create, as gh prints it: "GraphQL: <reason> (createPullRequest)". Then no PR exists.
function refusal(stderr) {
  const reason = prCause(/GraphQL: (.+?) \(createPullRequest\)/.exec(String(stderr))?.[1] ?? '');
  if (!reason) return null;
  return /Body is too long/i.test(reason)
    ? 'GitHub refused to open the PR: its description is too long (GitHub\'s limit is 65,536 characters). The branch is pushed; no PR was opened. Make the PR description shorter, then try again.'
    : `GitHub refused to open the PR: ${reason.replace(/\.$/, '')}. The branch is pushed; no PR was opened. Fix what GitHub names, then try again.`;
}

// The native runner records each gh call in the GitHub call ledger of its repository.
const counted = nativeGithubCounter((file, args, { cwd, input }) => execute(file, args,
  { cwd, input, encoding: 'utf8', shell: false, maxBuffer: 8 * 1024 * 1024 }));
function dependencies(ports = {}) {
  const run = ports.execFile ?? counted;
  async function raw(cwd, file, args, input) {
    let result;
    try { result = await run(file, args, { cwd, ...(input === undefined ? {} : { input }) }); }
    catch (error) {
      if (!Number.isInteger(error?.code) || error.code === 0) fail('workflow_github_command_unavailable');
      result = { code: error.code, stdout: error.stdout ?? '', stderr: error.stderr ?? '' };
    }
    if (!result || typeof result.stdout !== 'string'
      || result.code !== undefined && !Number.isInteger(result.code)) fail('workflow_github_command_invalid');
    return { code: result.code ?? 0, stdout: result.stdout, stderr: typeof result.stderr === 'string' ? result.stderr : '' };
  }
  async function command(cwd, file, args) {
    const result = await raw(cwd, file, args);
    // The tool's own error text rides along as detail, so the caller can name the real reason.
    if (result.code !== 0) throw Object.assign(new Error('workflow_github_command_failed'), { code: 'workflow_github_command_failed', detail: result.stderr });
    return result.stdout;
  }
  return { raw, command };
}

function originRepository(remote) {
  if (remote.startsWith('git@github.com:')) remote = 'https://github.com/' + remote.slice(15);
  let url;
  try { url = new URL(remote); } catch { fail('workflow_github_origin_invalid'); }
  if (url.hostname !== 'github.com' || url.port || url.search || url.hash || url.password
    || !['https:', 'ssh:'].includes(url.protocol)
    || url.username && !(url.protocol === 'ssh:' && url.username === 'git')) fail('workflow_github_origin_invalid');
  const name = url.pathname.slice(1).replace(/\.git$/, '');
  if (!repositoryName(name)) fail('workflow_github_origin_invalid');
  return name;
}

export function canonicalGithubUrl(value, repository, kind, number) {
  const match = typeof value === 'string' && /^https:\/\/github\.com\/([^/]+\/[^/]+)\/(issues|pull)\/([1-9][0-9]*)$/.exec(value);
  const n = match ? Number(match[3]) : 0;
  if (!Number.isSafeInteger(n) || n <= 0 || !sameRepo(match[1], repository) || match[2] !== kind) return 0;
  try {
    const url = new URL(value);
    const found = url.host === 'github.com' && !url.search && !url.hash && url.pathname === `/${match[1]}/${kind}/${match[3]}` ? n : 0;
    return number === undefined || found === number ? found : 0;
  } catch { return 0; }
}

async function repositoryAt(cwd, deps, expected) {
  if (!text(cwd)) fail('workflow_github_cwd_required');
  const remote = (await deps.command(cwd, 'git', ['remote', 'get-url', 'origin'])).trim();
  const repository = originRepository(remote);
  const actual = parseJson(await deps.command(cwd, 'gh', ['repo', 'view', repository,
    '--json', 'nameWithOwner,defaultBranchRef,url']));
  if (!repositoryName(actual?.nameWithOwner) || !sameRepo(actual.nameWithOwner, repository)
    || expected !== undefined && !sameRepo(actual.nameWithOwner, expected)
    || !text(actual.defaultBranchRef?.name) || actual.url !== `https://github.com/${actual.nameWithOwner}`)
    fail('workflow_github_repository_mismatch');
  return { repository: actual.nameWithOwner, defaultBranch: actual.defaultBranchRef.name };
}

function issueSelector(issue) {
  if (Number.isSafeInteger(issue) && issue > 0) return { number: issue };
  if (typeof issue !== 'string') fail('workflow_github_issue_invalid');
  let match = /^([1-9][0-9]*)$/.exec(issue);
  if (match) return { number: Number(match[1]) };
  match = /^([A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*)#([1-9][0-9]*)$/.exec(issue)
    ?? /^https:\/\/github\.com\/([A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*)\/issues\/([1-9][0-9]*)$/.exec(issue);
  if (!match) fail('workflow_github_issue_invalid');
  return { repository: match[1], number: Number(match[2]) };
}

export async function resolveWorkflowRepository({ cwd } = {}, ports = {}) {
  return repositoryAt(cwd, dependencies(ports));
}

export async function resolveWorkflowIssue(input, ports = {}) {
  const { cwd, issue } = structuredClone(input ?? {}), selected = issueSelector(issue);
  if (!Number.isSafeInteger(selected.number) || selected.number < 1) fail('workflow_github_issue_invalid');
  const deps = dependencies(ports), repo = await repositoryAt(cwd, deps);
  if (selected.repository && !sameRepo(selected.repository, repo.repository)) fail('workflow_github_issue_foreign');
  const actual = parseJson(await deps.command(cwd, 'gh', ['api', `repos/${repo.repository}/issues/${selected.number}`]));
  if (!actual || Object.hasOwn(actual, 'pull_request') || actual.number !== selected.number
    || !canonicalGithubUrl(actual.html_url, repo.repository, 'issues', selected.number)
    || typeof actual.title !== 'string' || !(actual.body === null || typeof actual.body === 'string'))
    fail('workflow_github_issue_mismatch');
  return { ...repo, issue: { number: actual.number, url: actual.html_url, title: actual.title, body: actual.body ?? '' } };
}

function markerBody(body, marker) {
  if (typeof body !== 'string') fail('workflow_github_body_invalid');
  const tokens = body.match(/pdd-workflow:[A-Za-z0-9_.-]+:[A-Za-z0-9_.-]+/g) ?? [];
  if (!tokens.length && !body.includes('pdd-workflow:')) return false;
  if ((body.match(/pdd-workflow:/g) ?? []).length !== 1 || tokens.length !== 1 || tokens[0] !== marker
    || body.split(/\r?\n/).filter(line => line === `<!-- ${marker} -->`).length !== 1)
    fail('workflow_github_marker_mismatch');
  return true;
}

async function localTopic(cwd, baseBranch, deps) {
  if (!text(baseBranch)) fail('workflow_github_topic_invalid');
  await deps.command(cwd, 'git', ['check-ref-format', '--branch', baseBranch]);
  const root = (await deps.command(cwd, 'git', ['rev-parse', '--show-toplevel'])).trim();
  if (!isAbsolute(root)) fail('workflow_github_root_invalid');
  const status = await deps.command(cwd, 'git', ['status', '--porcelain=v1', '-z', '--untracked-files=all']);
  if (status.split('\0').filter(Boolean).length)
    fail('workflow_github_worktree_dirty');
  const headBranch = (await deps.command(cwd, 'git', ['symbolic-ref', '--quiet', '--short', 'HEAD'])).trim();
  await deps.command(cwd, 'git', ['check-ref-format', '--branch', headBranch]);
  if (!text(headBranch) || headBranch === baseBranch) fail('workflow_github_topic_required');
  const headSha = (await deps.command(cwd, 'git', ['rev-parse', '--verify', 'HEAD'])).trim();
  if (!sha(headSha)) fail('workflow_github_head_invalid');
  const base = `refs/remotes/origin/${baseBranch}`;
  await deps.command(cwd, 'git', ['rev-parse', '--verify', `${base}^{commit}`]);
  const count = (await deps.command(cwd, 'git', ['rev-list', '--count', `${base}..HEAD`])).trim();
  if (!/^[1-9][0-9]*$/.test(count)) fail('workflow_github_topic_has_no_commits');
  return { headBranch, headSha };
}

export async function prepareWorkflowPr(input, ports = {}) {
  const { cwd, runId, stageId, repository, baseBranch, title: suppliedTitle } = structuredClone(input ?? {});
  if (!identifier(runId) || !identifier(stageId) || !repositoryName(repository)
    || suppliedTitle !== undefined && (!text(suppliedTitle) || suppliedTitle.length > 256)) fail('workflow_github_intent_invalid');
  const deps = dependencies(ports), actual = await repositoryAt(cwd, deps, repository);
  const topic = await localTopic(cwd, baseBranch, deps);
  const title = suppliedTitle ?? (await deps.command(cwd, 'git', ['log', '-1', '--format=%s'])).trim();
  if (!text(title) || title.length > 256) fail('workflow_github_title_invalid');
  const marker = `pdd-workflow:${runId}:${stageId}`;
  return { repository: actual.repository, runId, stageId, ...topic, baseBranch, marker, title };
}

function intentCopy(value) {
  const intent = structuredClone(value);
  if (!intent || Object.keys(intent).sort().join(',') !== 'baseBranch,headBranch,headSha,marker,repository,runId,stageId,title'
    || !repositoryName(intent.repository) || !identifier(intent.runId) || !identifier(intent.stageId)
    || intent.marker !== `pdd-workflow:${intent.runId}:${intent.stageId}` || !sha(intent.headSha)
    || !text(intent.headBranch) || !text(intent.baseBranch) || intent.headBranch === intent.baseBranch
    || !text(intent.title)) fail('workflow_github_intent_invalid');
  return intent;
}

function actualPr(row, intent) {
  if (!row || !Number.isSafeInteger(row.number) || row.number < 1 || row.isCrossRepository !== false
    || !sameRepo(`${row.headRepositoryOwner?.login}/${row.headRepository?.name}`, intent.repository)
    || !canonicalGithubUrl(row.url, intent.repository, 'pull', row.number)
    || row.headRefName !== intent.headBranch || row.baseRefName !== intent.baseBranch || row.headRefOid !== intent.headSha
    || !markerBody(row.body, intent.marker) || !['OPEN', 'MERGED', 'CLOSED'].includes(row.state)
    || row.state === 'MERGED' && !sha(row.mergeCommit?.oid)) fail('workflow_github_pr_mismatch');
  return { repository: intent.repository, number: row.number, url: row.url, headBranch: row.headRefName,
    baseBranch: row.baseRefName, headSha: row.headRefOid, mergeCommit: row.state === 'MERGED' ? row.mergeCommit.oid : null };
}

async function lookup(cwd, intent, deps, draft = false) {
  try {
    const prefix = ['pr', 'list', '--repo', intent.repository, '--state', 'all', '--limit', '100', '--json', fields];
    const responses = [];
    // Search the marker across branches as well as the actual head, including closed/merged PRs.
    for (const selector of [['--search', `"${intent.marker}" in:body`], ['--head', intent.headBranch]]) {
      const rows = parseJson(await deps.command(cwd, 'gh', [...prefix, ...selector]));
      if (!Array.isArray(rows) || rows.length >= 100) fail('workflow_github_lookup_incomplete');
      responses.push(...rows);
    }
    const unique = new Map();
    for (const row of responses) {
      const previous = unique.get(row.number);
      if (previous && JSON.stringify(previous) !== JSON.stringify(row)) fail('workflow_github_lookup_changed');
      unique.set(row.number, row);
    }
    if (!unique.size) return { state: 'absent' };
    if (unique.size !== 1) fail('workflow_github_pr_ambiguous');
    const row = [...unique.values()][0], pr = actualPr(row, intent);
    if (draft && row.isDraft !== true) return { state: 'found', outcome: outcome('recovery_required', 'The original PR is not confirmed as a draft. Inspect the existing PR; do not convert it or publish again.') };
    return { state: 'found', outcome: outcome(row.state.toLowerCase(), 'Verified the original workflow pull request.', pr) };
  } catch { return { state: 'refused' }; }
}

export async function reconcileWorkflowPr(input, ports = {}) {
  try {
    const { cwd, intent: supplied, draft = false } = structuredClone(input ?? {});
    if (typeof draft !== 'boolean') fail('workflow_github_draft_invalid');
    const intent = intentCopy(supplied), deps = dependencies(ports);
    await repositoryAt(cwd, deps, intent.repository);
    const found = await lookup(cwd, intent, deps, draft);
    if (found.state === 'found') return found.outcome;
  } catch { /* Read failure never authorizes another push or create. */ }
  return outcome('recovery_required', 'The original pull request is missing, changed, ambiguous or unreadable. Reconcile this same intent; do not publish again.');
}

export async function publishWorkflowPr(input, ports = {}) {
  let effectStarted = false, unpublishedOnly = false;
  try {
    const { cwd, intent: supplied, body, unpublishedOnly: mode = false, draft = false } = structuredClone(input ?? {});
    if (typeof draft !== 'boolean') fail('workflow_github_draft_invalid');
    if (typeof mode !== 'boolean') fail('workflow_github_recovery_mode_invalid');
    unpublishedOnly = mode;
    const intent = intentCopy(supplied), deps = dependencies(ports);
    if (!markerBody(body, intent.marker)) fail('workflow_github_marker_missing');
    if (characters(body) > PR_BODY_LIMIT) return outcome('failed', `The PR description has ${characters(body).toLocaleString('en-US')} characters. GitHub accepts at most 65,536. Nothing was pushed. Make it shorter, then try again.`);
    await repositoryAt(cwd, deps, intent.repository);
    const found = await lookup(cwd, intent, deps, draft);
    if (found.state === 'found') return unpublishedOnly
      ? outcome('recovery_required', 'An original PR already exists. Inspect it without unpublished-only publication.') : found.outcome;
    if (found.state !== 'absent') return outcome('recovery_required', 'Cannot confirm the original PR identity. Reconcile the saved intent without another publication.');
    const readPushRemote = async () => (await deps.command(cwd, 'git', ['remote', 'get-url', '--push', '--all', 'origin'])).trim();
    const topic = await localTopic(cwd, intent.baseBranch, deps);
    if (topic.headBranch !== intent.headBranch || topic.headSha !== intent.headSha) fail('workflow_github_source_changed');
    const pushRemote = await readPushRemote();
    if (!sameRepo(originRepository(pushRemote), intent.repository)) fail('workflow_github_repository_mismatch');
    if (unpublishedOnly) {
      const remote = await deps.raw(cwd, 'git', ['ls-remote', '--exit-code', '--refs', 'origin', `refs/heads/${intent.headBranch}`]);
      if (remote.code !== 2 || remote.stdout !== '')
        return outcome('recovery_required', 'The saved remote branch is present or its absence is unconfirmed. Inspect the same intent without publication.');
      // Remote reads can wait for authentication. Revalidate source and body after that boundary.
      const current = await localTopic(cwd, intent.baseBranch, deps);
      if (current.headBranch !== intent.headBranch || current.headSha !== intent.headSha
        || !markerBody(body, intent.marker)) fail('workflow_github_source_changed');
      await repositoryAt(cwd, deps, intent.repository);
      if (await readPushRemote() !== pushRemote) fail('workflow_github_repository_mismatch');
    }
    // An earlier attempt may have pushed this exact SHA before GitHub refused the PR: do not push it again.
    const remote = unpublishedOnly ? null : await deps.raw(cwd, 'git', ['ls-remote', '--exit-code', '--refs', 'origin', `refs/heads/${intent.headBranch}`]);
    effectStarted = true;
    if (remote?.code !== 0 || remote.stdout.trim() !== `${intent.headSha}\trefs/heads/${intent.headBranch}`)
      await deps.command(cwd, 'git', ['push', 'origin', `${intent.headSha}:refs/heads/${intent.headBranch}`]);
    const created = await deps.raw(cwd, 'gh', ['pr', 'create', '--repo', intent.repository, '--head', intent.headBranch,
      '--base', intent.baseBranch, '--title', intent.title, '--body-file', '-', ...(draft ? ['--draft'] : [])], body);
    if (created.code !== 0) {
      // Read back first: an exact PR wins. Only GitHub's own refusal with no PR is certain; anything else stays unconfirmed.
      const found = await lookup(cwd, intent, deps, draft);
      if (found.state === 'found') return found.outcome;
      const refused = found.state === 'absent' && refusal(created.stderr), line = ghLine(created.stderr);
      return refused ? outcome('rejected', refused)
        : outcome('recovery_required', `PR creation is unconfirmed${line ? ` (gh: ${line})` : ''}. Reconcile this same saved intent; do not publish again.`);
    }
    // A successful create exit/printed URL is insufficient; use genuine GitHub readback.
    return await reconcileWorkflowPr({ cwd, intent, draft }, ports);
  } catch {
    return effectStarted || unpublishedOnly
      ? outcome('recovery_required', 'Push or PR creation is unconfirmed. Reconcile this same saved intent; do not publish again.')
      : outcome('failed', 'Publication did not start. Check the saved intent, repository, clean topic branch and marked body.');
  }
}

export async function readWorkflowPrStatus(input, ports = {}) {
  try {
    const { cwd, url, view = false, includeDraft = false } = structuredClone(input ?? {});
    if (!text(url) || !/^https:\/\/github\.com\/[^/]+\/[^/]+\/pull\/[1-9][0-9]*$/.test(url)) fail('workflow_github_pr_url_invalid');
    // With `view`, the same one read also gives the description, the head and the comments (a readable-top refresh).
    const row = parseJson(await dependencies(ports).command(cwd, 'gh', ['pr', 'view', url, '--json', `state,mergedAt,statusCheckRollup,baseRefName,headRefOid${view ? ',body,comments' : ''}${includeDraft ? ',isDraft' : ''}`]));
    const state = { OPEN: 'open', MERGED: 'merged', CLOSED: 'closed' }[row?.state];
    if (!state) fail('workflow_github_pr_state_invalid');
    const checks = Array.isArray(row.statusCheckRollup) ? row.statusCheckRollup : [];
    const outcome = check => String(check?.conclusion ?? check?.state ?? '').toUpperCase();
    const ci = !checks.length ? 'none'
      : checks.some(check => ['FAILURE', 'CANCELLED', 'TIMED_OUT', 'ERROR', 'ACTION_REQUIRED', 'STARTUP_FAILURE'].includes(outcome(check))) ? 'failing'
      : checks.some(check => !['SUCCESS', 'NEUTRAL', 'SKIPPED'].includes(outcome(check))) ? 'pending' : 'passing';
    return { state, ci, ...(includeDraft ? { draft: typeof row.isDraft === 'boolean' ? row.isDraft : null } : {}), ...(text(row.baseRefName) ? { base: row.baseRefName } : {}),
      ...(text(row.headRefOid) ? { headSha: row.headRefOid } : {}),
      ...(view ? { view: { body: typeof row.body === 'string' ? row.body : null, head: text(row.headRefOid) ? row.headRefOid : null, comments: Array.isArray(row.comments) ? row.comments : null } } : {}) };
  } catch { return { state: 'unknown', ci: 'unknown' }; }
}

// The independent checker verdict (pdd-check) for one PR head: a JSON block with verdict PASS, FAIL or NOT SURE and the
// exact head SHA, in a comment by the repository owner, a member or a collaborator. When those comments give different
// verdicts for the same head, the verdict is 'split' (with the verdicts), never the newest one. Any doubt gives null.
// `comments` from `gh pr view --json comments` (GraphQL names) replace the REST read, so no other call is made.
export async function readWorkflowPrChecker(input, ports = {}) {
  try {
    const { cwd, url, headSha, comments } = structuredClone(input ?? {});
    const match = /^https:\/\/github\.com\/([^/]+)\/([^/]+)\/pull\/([1-9][0-9]*)$/.exec(String(url ?? ''));
    if (!match || !/^[a-f0-9]{40}$/i.test(String(headSha ?? ''))) return null;
    const rows = Array.isArray(comments) ? comments : (await dependencies(ports).command(cwd, 'gh', ['api', '--paginate', `repos/${match[1]}/${match[2]}/issues/${match[3]}/comments?per_page=100`, '--jq', '.[] | {body, author_association, html_url, created_at}']))
      .split('\n').filter(row => row.trim()).map(line => { try { return JSON.parse(line); } catch { return null; } });
    let latest = null;
    const seen = new Set();
    for (const comment of rows) {
      const association = comment?.author_association ?? comment?.authorAssociation, link = comment?.html_url ?? comment?.url, at = String(comment?.created_at ?? comment?.createdAt ?? '');
      if (!['OWNER', 'MEMBER', 'COLLABORATOR'].includes(association) || typeof comment.body !== 'string') continue;
      for (const block of comment.body.matchAll(/```(?:json)?\s*([\s\S]*?)```/g)) {
        let check;
        try { check = JSON.parse(block[1]); } catch { continue; }
        if (!['PASS', 'FAIL', 'NOT SURE'].includes(check?.verdict) || String(check.head ?? '').toLowerCase() !== headSha.toLowerCase()) continue;
        seen.add(check.verdict);
        if (!latest || at >= latest.at) latest = { verdict: check.verdict, url: text(link) ? link : null, at };
      }
    }
    if (seen.size > 1) return { verdict: 'split', verdicts: ['PASS', 'FAIL', 'NOT SURE'].filter(verdict => seen.has(verdict)), url: latest.url };
    return latest && { verdict: latest.verdict, url: latest.url };
  } catch { return null; }
}
