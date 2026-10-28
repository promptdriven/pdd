// Generated from prompts/cli/workflow-github.prompt.md (sha256: b07dbb564fefe8169e6be5c96c178d68e1858dea4ff3baccd010b6d06492d21d).
import { execFile } from 'node:child_process';
import { constants } from 'node:fs';
import { lstat, open, readFile, realpath } from 'node:fs/promises';
import { dirname, isAbsolute, relative, resolve, sep } from 'node:path';
import { promisify } from 'node:util';
import { causeText } from './runtime-output.mjs';

const execute = promisify(execFile);
const fields = 'number,url,state,headRefName,baseRefName,headRefOid,mergeCommit,body,isCrossRepository,headRepository,headRepositoryOwner';
const identifier = value => typeof value === 'string' && /^[A-Za-z0-9][A-Za-z0-9_.-]{0,159}$/.test(value);
const text = value => typeof value === 'string' && value.length > 0 && !/[\u0000-\u001f\u007f]/u.test(value);
const repositoryName = value => text(value) && /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/.test(value);
const sha = value => typeof value === 'string' && /^[a-f0-9]{40}$/.test(value);
const sameRepo = (a, b) => typeof a === 'string' && typeof b === 'string' && a.toLowerCase() === b.toLowerCase();
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

function dependencies(ports = {}) {
  const run = ports.execFile ?? ((file, args, { cwd }) => execute(file, args,
    { cwd, encoding: 'utf8', shell: false, maxBuffer: 8 * 1024 * 1024 }));
  async function raw(cwd, file, args) {
    let result;
    try { result = await run(file, args, { cwd }); }
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
  return { raw, command, readFile: ports.readFile ?? ((file, encoding) => readFile(file,
    { encoding, flag: constants.O_RDONLY | constants.O_NOFOLLOW })),
  async writeFile(file, body, encoding) {
    await assertBodyPath(file);
    return (ports.writeFile ?? writeBodyFile)(file, body, encoding);
  } };
}


async function assertBodyPath(file) {
  if (await realpath(dirname(file)) !== dirname(file)) fail('workflow_github_body_unsafe');
  try {
    const entry = await lstat(file);
    if (!entry.isFile() || entry.nlink !== 1) fail('workflow_github_body_unsafe');
    return entry;
  } catch (error) { if (error?.code !== 'ENOENT') throw error; }
}

async function writeBodyFile(file, body, encoding) {
  // Open without truncation or following the final link; validate the opened file before modifying it.
  const handle = await open(file, constants.O_WRONLY | constants.O_CREAT | constants.O_NOFOLLOW, 0o666);
  try {
    const opened = await handle.stat(), entry = await assertBodyPath(file);
    if (!opened.isFile() || opened.nlink !== 1 || opened.dev !== entry?.dev || opened.ino !== entry?.ino)
      fail('workflow_github_body_unsafe');
    await handle.truncate(0);
    await handle.writeFile(body, encoding);
  } finally { await handle.close(); }
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

function canonicalUrl(value, repository, kind, number) {
  try {
    const url = new URL(value);
    const match = /^\/([^/]+\/[^/]+)\/(issues|pull)\/([1-9][0-9]*)$/.exec(url.pathname);
    return url.protocol === 'https:' && url.host === 'github.com' && !url.username && !url.password
      && !url.search && !url.hash && match && sameRepo(match[1], repository)
      && match[2] === kind && Number(match[3]) === number;
  } catch { return false; }
}

async function repositoryAt(cwd, deps) {
  if (!text(cwd)) fail('workflow_github_cwd_required');
  const remote = (await deps.command(cwd, 'git', ['remote', 'get-url', 'origin'])).trim();
  const repository = originRepository(remote);
  const actual = parseJson(await deps.command(cwd, 'gh', ['repo', 'view', repository,
    '--json', 'nameWithOwner,defaultBranchRef,url']));
  if (!repositoryName(actual?.nameWithOwner) || !sameRepo(actual.nameWithOwner, repository)
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

export async function resolveWorkflowIssue(input, ports = {}) {
  const { cwd, issue } = structuredClone(input ?? {}), selected = issueSelector(issue);
  if (!Number.isSafeInteger(selected.number) || selected.number < 1) fail('workflow_github_issue_invalid');
  const deps = dependencies(ports), repo = await repositoryAt(cwd, deps);
  if (selected.repository && !sameRepo(selected.repository, repo.repository)) fail('workflow_github_issue_foreign');
  const actual = parseJson(await deps.command(cwd, 'gh', ['api', `repos/${repo.repository}/issues/${selected.number}`]));
  if (!actual || Object.hasOwn(actual, 'pull_request') || actual.number !== selected.number
    || !canonicalUrl(actual.html_url, repo.repository, 'issues', selected.number)
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

async function localTopic(cwd, baseBranch, bodyFile, deps) {
  if (!text(baseBranch) || !text(bodyFile)) fail('workflow_github_topic_invalid');
  await assertBodyPath(bodyFile);
  await deps.command(cwd, 'git', ['check-ref-format', '--branch', baseBranch]);
  const root = (await deps.command(cwd, 'git', ['rev-parse', '--show-toplevel'])).trim();
  if (!isAbsolute(root)) fail('workflow_github_root_invalid');
  const bodyRelative = relative(root, bodyFile), inside = bodyRelative && bodyRelative !== '..'
    && !bodyRelative.startsWith('..' + sep) && !isAbsolute(bodyRelative);
  if (inside) {
    const tracked = await deps.raw(cwd, 'git', ['ls-files', '--error-unmatch', '--', bodyRelative]);
    if (tracked.code !== 1) fail('workflow_github_body_must_be_untracked');
  }
  const status = await deps.command(cwd, 'git', ['status', '--porcelain=v1', '-z', '--untracked-files=all']);
  if (status.split('\0').filter(Boolean).some(row => !(inside && row === '?? ' + bodyRelative)))
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
  const { cwd, runId, stageId, repository, baseBranch, bodyFile, title: suppliedTitle } = structuredClone(input ?? {});
  if (!identifier(runId) || !identifier(stageId) || !repositoryName(repository) || !text(bodyFile)
    || suppliedTitle !== undefined && (!text(suppliedTitle) || suppliedTitle.length > 256)) fail('workflow_github_intent_invalid');
  const deps = dependencies(ports), actual = await repositoryAt(cwd, deps);
  if (!sameRepo(repository, actual.repository)) fail('workflow_github_repository_mismatch');
  const file = resolve(cwd, bodyFile), topic = await localTopic(cwd, baseBranch, file, deps);
  const title = suppliedTitle ?? (await deps.command(cwd, 'git', ['log', '-1', '--format=%s'])).trim();
  if (!text(title) || title.length > 256) fail('workflow_github_title_invalid');
  const marker = `pdd-workflow:${runId}:${stageId}`;
  let body;
  try { body = await deps.readFile(file, 'utf8'); }
  catch (error) { if (error?.code !== 'ENOENT') throw error; body = title + '\n'; }
  if (!markerBody(body, marker)) body += (body.endsWith('\n') ? '\n' : '\n\n') + `<!-- ${marker} -->\n`;
  await deps.writeFile(file, body, 'utf8');
  return { repository: actual.repository, runId, stageId, ...topic, baseBranch, marker, title, bodyFile: file };
}

function intentCopy(value) {
  const intent = structuredClone(value);
  if (!intent || Object.keys(intent).sort().join(',') !== 'baseBranch,bodyFile,headBranch,headSha,marker,repository,runId,stageId,title'
    || !repositoryName(intent.repository) || !identifier(intent.runId) || !identifier(intent.stageId)
    || intent.marker !== `pdd-workflow:${intent.runId}:${intent.stageId}` || !sha(intent.headSha)
    || !text(intent.headBranch) || !text(intent.baseBranch) || intent.headBranch === intent.baseBranch
    || !text(intent.title) || !text(intent.bodyFile) || !isAbsolute(intent.bodyFile)) fail('workflow_github_intent_invalid');
  return intent;
}

function actualPr(row, intent) {
  if (!row || !Number.isSafeInteger(row.number) || row.number < 1 || row.isCrossRepository !== false
    || !sameRepo(`${row.headRepositoryOwner?.login}/${row.headRepository?.name}`, intent.repository)
    || !canonicalUrl(row.url, intent.repository, 'pull', row.number)
    || row.headRefName !== intent.headBranch || row.baseRefName !== intent.baseBranch || row.headRefOid !== intent.headSha
    || !markerBody(row.body, intent.marker) || !['OPEN', 'MERGED', 'CLOSED'].includes(row.state)
    || row.state === 'MERGED' && !sha(row.mergeCommit?.oid)) fail('workflow_github_pr_mismatch');
  return { repository: intent.repository, number: row.number, url: row.url, headBranch: row.headRefName,
    baseBranch: row.baseRefName, headSha: row.headRefOid, mergeCommit: row.state === 'MERGED' ? row.mergeCommit.oid : null };
}

async function lookup(cwd, intent, deps) {
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
    return { state: 'found', outcome: outcome(row.state.toLowerCase(), 'Verified the original workflow pull request.', pr) };
  } catch { return { state: 'refused' }; }
}

export async function reconcileWorkflowPr(input, ports = {}) {
  try {
    const { cwd, intent: supplied } = structuredClone(input ?? {}), intent = intentCopy(supplied), deps = dependencies(ports);
    const actual = await repositoryAt(cwd, deps);
    if (!sameRepo(actual.repository, intent.repository)) fail('workflow_github_repository_mismatch');
    const found = await lookup(cwd, intent, deps);
    if (found.state === 'found') return found.outcome;
  } catch { /* Read failure never authorizes another push or create. */ }
  return outcome('recovery_required', 'The original pull request is missing, changed, ambiguous or unreadable. Reconcile this same intent; do not publish again.');
}

export async function publishWorkflowPr(input, ports = {}) {
  let effectStarted = false, unpublishedOnly = false;
  try {
    const { cwd, intent: supplied, unpublishedOnly: mode = false } = structuredClone(input ?? {});
    if (typeof mode !== 'boolean') fail('workflow_github_recovery_mode_invalid');
    unpublishedOnly = mode;
    const intent = intentCopy(supplied), deps = dependencies(ports);
    const actual = await repositoryAt(cwd, deps);
    if (!sameRepo(actual.repository, intent.repository)) fail('workflow_github_repository_mismatch');
    const found = await lookup(cwd, intent, deps);
    if (found.state === 'found') return unpublishedOnly
      ? outcome('recovery_required', 'An original PR already exists. Inspect it without unpublished-only publication.') : found.outcome;
    if (found.state !== 'absent') return outcome('recovery_required', 'Cannot confirm the original PR identity. Reconcile the saved intent without another publication.');
    const topic = await localTopic(cwd, intent.baseBranch, intent.bodyFile, deps);
    if (topic.headBranch !== intent.headBranch || topic.headSha !== intent.headSha) fail('workflow_github_source_changed');
    const body = await deps.readFile(intent.bodyFile, 'utf8');
    if (!markerBody(body, intent.marker)) fail('workflow_github_marker_missing');
    if (characters(body) > PR_BODY_LIMIT) return outcome('failed', `The PR description has ${characters(body).toLocaleString('en-US')} characters. GitHub accepts at most 65,536. Nothing was pushed. Make it shorter, then try again.`);
    const pushRemote = (await deps.command(cwd, 'git', ['remote', 'get-url', '--push', '--all', 'origin'])).trim();
    if (!sameRepo(originRepository(pushRemote), intent.repository)) fail('workflow_github_repository_mismatch');
    if (unpublishedOnly) {
      const remote = await deps.raw(cwd, 'git', ['ls-remote', '--exit-code', '--refs', 'origin', `refs/heads/${intent.headBranch}`]);
      if (remote.code !== 2 || remote.stdout !== '')
        return outcome('recovery_required', 'The saved remote branch is present or its absence is unconfirmed. Inspect the same intent without publication.');
      // Remote reads can wait for authentication. Revalidate source and body after that boundary.
      const current = await localTopic(cwd, intent.baseBranch, intent.bodyFile, deps);
      if (current.headBranch !== intent.headBranch || current.headSha !== intent.headSha
        || await deps.readFile(intent.bodyFile, 'utf8') !== body) fail('workflow_github_source_changed');
      const currentRepo = await repositoryAt(cwd, deps);
      if (!sameRepo(currentRepo.repository, intent.repository)
        || (await deps.command(cwd, 'git', ['remote', 'get-url', '--push', '--all', 'origin'])).trim() !== pushRemote)
        fail('workflow_github_repository_mismatch');
    }
    // An earlier attempt may have pushed this exact SHA before GitHub refused the PR: do not push it again.
    const remote = unpublishedOnly ? null : await deps.raw(cwd, 'git', ['ls-remote', '--exit-code', '--refs', 'origin', `refs/heads/${intent.headBranch}`]);
    effectStarted = true;
    if (remote?.code !== 0 || remote.stdout.trim() !== `${intent.headSha}\trefs/heads/${intent.headBranch}`)
      await deps.command(cwd, 'git', ['push', 'origin', `${intent.headSha}:refs/heads/${intent.headBranch}`]);
    const created = await deps.raw(cwd, 'gh', ['pr', 'create', '--repo', intent.repository, '--head', intent.headBranch,
      '--base', intent.baseBranch, '--title', intent.title, '--body-file', intent.bodyFile]);
    if (created.code !== 0) {
      // Read back first: an exact PR wins. Only GitHub's own refusal with no PR is certain; anything else stays unconfirmed.
      const found = await lookup(cwd, intent, deps);
      if (found.state === 'found') return found.outcome;
      const refused = found.state === 'absent' && refusal(created.stderr), line = ghLine(created.stderr);
      return refused ? outcome('rejected', refused)
        : outcome('recovery_required', `PR creation is unconfirmed${line ? ` (gh: ${line})` : ''}. Reconcile this same saved intent; do not publish again.`);
    }
    // A successful create exit/printed URL is insufficient; use genuine GitHub readback.
    return await reconcileWorkflowPr({ cwd, intent }, ports);
  } catch {
    return effectStarted || unpublishedOnly
      ? outcome('recovery_required', 'Push or PR creation is unconfirmed. Reconcile this same saved intent; do not publish again.')
      : outcome('failed', 'Publication did not start. Check the saved intent, repository, clean topic branch and marked body file.');
  }
}

export async function readWorkflowPrStatus(input, ports = {}) {
  try {
    const { cwd, url } = structuredClone(input ?? {});
    if (!text(url) || !/^https:\/\/github\.com\/[^/]+\/[^/]+\/pull\/[1-9][0-9]*$/.test(url)) fail('workflow_github_pr_url_invalid');
    const row = parseJson(await dependencies(ports).command(cwd, 'gh', ['pr', 'view', url, '--json', 'state,mergedAt,statusCheckRollup']));
    const state = { OPEN: 'open', MERGED: 'merged', CLOSED: 'closed' }[row?.state];
    if (!state) fail('workflow_github_pr_state_invalid');
    const checks = Array.isArray(row.statusCheckRollup) ? row.statusCheckRollup : [];
    const outcome = check => String(check?.conclusion ?? check?.state ?? '').toUpperCase();
    const ci = !checks.length ? 'none'
      : checks.some(check => ['FAILURE', 'CANCELLED', 'TIMED_OUT', 'ERROR', 'ACTION_REQUIRED', 'STARTUP_FAILURE'].includes(outcome(check))) ? 'failing'
      : checks.some(check => !['SUCCESS', 'NEUTRAL', 'SKIPPED'].includes(outcome(check))) ? 'pending' : 'passing';
    return { state, ci };
  } catch { return { state: 'unknown', ci: 'unknown' }; }
}
