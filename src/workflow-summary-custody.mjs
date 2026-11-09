// Generated from prompts/cli/workflow-runner.prompt.md (sha256: 47f261baa0f2894bae32d6cba49262a456808354cf77dfdf05407c4cc4b7fa5c).
// Supplemental summary comment and PR-body write custody for workflow-runner.
// Every write has durable intent first; a lost result is reconciled by reads only.
import { createHash, randomUUID } from 'node:crypto';
import { closeSync, fsyncSync, lstatSync, openSync, readFileSync, renameSync, unlinkSync, writeFileSync } from 'node:fs';
import { hostname } from 'node:os';
import { join } from 'node:path';
import { SUMMARY_RECOVERY_LINK_RESERVE, summaryRecoveryIndex } from './workflow-summary-recovery.mjs';

const digest = text => createHash('sha256').update(text).digest('hex');
const size = text => [...text].length;
const reject = message => { throw Error(message); };
function identity(run, pr) {
  if (!run || typeof run.root !== 'string' || typeof run.runDir !== 'string'
      || !/^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/.test(run.repo ?? '')
      || !Number.isSafeInteger(pr?.number) || pr.number < 1
      || pr.url !== `https://github.com/${run.repo}/pull/${pr.number}`)
    reject('Summary recovery requires the confirmed same-repository PR identity.');
  return { root: run.root, dir: run.runDir, repo: run.repo, number: pr.number, url: pr.url };
}
function regular(path) {
  const stat = lstatSync(path);
  if (!stat.isFile() || stat.isSymbolicLink() || stat.nlink !== 1) reject('Summary recovery custody is not a regular file.');
}
function save(path, state) {
  const temp = `${path}.${randomUUID()}.tmp`;
  let fd;
  try {
    fd = openSync(temp, 'wx', 0o600);
    writeFileSync(fd, JSON.stringify(state));
    fsyncSync(fd); closeSync(fd); fd = undefined;
    renameSync(temp, path);
    const directory = openSync(join(path, '..'), 'r');
    try { fsyncSync(directory); } finally { closeSync(directory); }
  } finally {
    if (fd !== undefined) closeSync(fd);
    try { unlinkSync(temp); } catch { /* The temporary file was renamed or never created. */ }
  }
}
async function locked(id, task) {
  const path = join(id.dir, `summary-recovery-${id.number}.json`), lock = `${path}.lock`;
  const owner = JSON.stringify({ pid: process.pid, host: hostname(), token: randomUUID() });
  let fd;
  try {
    try { fd = openSync(lock, 'wx', 0o600); }
    catch (error) {
      if (error.code !== 'EEXIST') throw error;
      // A crashed local owner may be reclaimed, but only while holding a
      // separate claim and after checking the same owner is still dead.
      const claim = `${lock}.reclaim`, claimFd = openSync(claim, 'wx', 0o600);
      try {
        regular(lock);
        const bytes = readFileSync(lock, 'utf8'), prior = JSON.parse(bytes);
        if (prior.host !== hostname() || !Number.isSafeInteger(prior.pid) || prior.pid <= 0 || typeof prior.token !== 'string') throw Error('uncertain owner');
        try { process.kill(prior.pid, 0); throw Error('live owner'); }
        catch (probe) { if (probe.code !== 'ESRCH') throw probe; }
        if (readFileSync(lock, 'utf8') !== bytes) throw Error('changed owner');
        unlinkSync(lock);
        fd = openSync(lock, 'wx', 0o600);
      } finally { closeSync(claimFd); unlinkSync(claim); }
    }
    writeFileSync(fd, owner); fsyncSync(fd);
  } catch { if (fd !== undefined) closeSync(fd); reject('Summary recovery custody is busy or unavailable; inspect the existing operation.'); }
  try {
    let state;
    try { regular(path); state = JSON.parse(readFileSync(path, 'utf8')); }
    catch (error) { if (error.code !== 'ENOENT') throw Error('Summary recovery custody is unreadable; inspect the existing operation.'); state = { version: 1, repository: id.repo, number: id.number, writes: {}, edit: null }; }
    if (!state || state.version !== 1 || state.repository !== id.repo || state.number !== id.number
        || !state.writes || typeof state.writes !== 'object' || Array.isArray(state.writes))
      reject('Summary recovery custody is invalid; inspect the existing operation.');
    return await task(state, () => save(path, state));
  } finally {
    closeSync(fd);
    try { if (readFileSync(lock, 'utf8') === owner) unlinkSync(lock); } catch { /* Never erase another claim. */ }
  }
}
async function command(execFile, id, args, input) {
  const result = await execFile('gh', args, { cwd: id.root, ...(input === undefined ? {} : { input }) });
  if (!result || typeof result.stdout !== 'string' || result.code !== undefined && result.code !== 0) throw Error('GitHub request failed.');
  return result.stdout;
}
async function actor(execFile, id) {
  const login = (await command(execFile, id, ['api', 'user', '--jq', '.login'])).trim();
  if (!/^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/.test(login)) reject('The publishing actor could not be confirmed.');
  return login;
}
function validCommentUrl(value, id) {
  try {
    const url = new URL(value), match = /^\/([^/]+\/[^/]+)\/(?:pull|issues)\/([1-9][0-9]*)$/.exec(url.pathname);
    return url.protocol === 'https:' && url.host === 'github.com' && !url.username && !url.password && !url.search
      && match && match[1].toLowerCase() === id.repo.toLowerCase() && Number(match[2]) === id.number
      && /^#issuecomment-[1-9][0-9]*$/.test(url.hash);
  } catch { return false; }
}
async function comments(execFile, id) {
  const output = await command(execFile, id, ['api', '--paginate', '--slurp', `repos/${id.repo}/issues/${id.number}/comments?per_page=100`]);
  let pages; try { pages = JSON.parse(output); } catch { reject('Summary comments could not be read completely.'); }
  if (!Array.isArray(pages) || !pages.every(Array.isArray)) reject('Summary comments could not be read completely.');
  return pages.flat();
}
function matches(rows, body, login, id) {
  return rows.filter(row => row && row.body === body && typeof row.user?.login === 'string'
    && row.user.login.toLowerCase() === login.toLowerCase() && validCommentUrl(row.html_url, id));
}
async function comment(execFile, id, state, persist, login, body) {
  if (typeof body !== 'string' || !body || size(body) > 60000) reject('A summary recovery comment exceeds its budget.');
  const key = digest(body), old = state.writes[key];
  if (old && (old.body !== body || old.actor !== login || !['intent', 'confirmed'].includes(old.state)))
    reject('Summary recovery custody conflicts with this comment.');
  let found = matches(await comments(execFile, id), body, login, id);
  if (found.length > 1) reject('Summary recovery comment is ambiguous.');
  if (found.length === 1) {
    state.writes[key] = { state: 'confirmed', actor: login, body, url: found[0].html_url }; persist();
    return found[0].html_url;
  }
  if (old) reject('Summary recovery comment write is unconfirmed; inspect the original write before retrying.');
  state.writes[key] = { state: 'intent', actor: login, body }; persist();
  try { await command(execFile, id, ['api', '--method', 'POST', `repos/${id.repo}/issues/${id.number}/comments`, '--input', '-'], JSON.stringify({ body })); }
  catch { /* A rejected or lost response cannot prove that GitHub made no comment. */ }
  found = matches(await comments(execFile, id), body, login, id);
  if (found.length !== 1) reject('Summary recovery comment write is unconfirmed; inspect the original write before retrying.');
  state.writes[key] = { state: 'confirmed', actor: login, body, url: found[0].html_url }; persist();
  return found[0].html_url;
}

// The planner reserves every index link before the first comment write.
export async function publishSummaryRecovery({ run, pr, plan }, { execFile }) {
  const id = identity(run, pr);
  if (typeof execFile !== 'function' || !plan || !Array.isArray(plan.chunks) || !plan.chunks.length
      || plan.chunks.some(body => typeof body !== 'string' || !body || size(body) > 60000))
    reject('Summary recovery plan is invalid.');
  summaryRecoveryIndex(plan, plan.chunks.map(() => 'x'.repeat(SUMMARY_RECOVERY_LINK_RESERVE)));
  return locked(id, async (state, persist) => {
    const login = await actor(execFile, id), links = [];
    for (const body of plan.chunks) links.push(await comment(execFile, id, state, persist, login, body));
    const body = summaryRecoveryIndex(plan, links);
    return comment(execFile, id, state, persist, login, body);
  });
}

async function readBody(execFile, id) {
  const output = await command(execFile, id, ['pr', 'view', id.url, '--json', 'body']);
  let row; try { row = JSON.parse(output); } catch { reject('The PR description could not be read.'); }
  if (typeof row?.body !== 'string') reject('The PR description could not be read.');
  return row.body;
}
// An unresolved prior edit blocks any new edit unless an exact read-back proves it.
export async function editSummaryRecoveryBody({ run, pr, body }, { execFile }) {
  const id = identity(run, pr);
  if (typeof execFile !== 'function' || typeof body !== 'string' || size(body) > 60000) reject('The PR description exceeds its recovery budget.');
  return locked(id, async (state, persist) => {
    let current = await readBody(execFile, id);
    if (state.edit?.state === 'intent') {
      if (current !== state.edit.body) reject('The previous PR description edit is unconfirmed; inspect it before retrying.');
      state.edit = { ...state.edit, state: 'confirmed' }; persist();
    }
    if (current === body) return;
    state.edit = { state: 'intent', body }; persist();
    try { await command(execFile, id, ['pr', 'edit', id.url, '--body-file', '-'], body); }
    catch { /* Only read-back can resolve an unknown edit. */ }
    current = await readBody(execFile, id);
    if (current !== body) reject('The PR description edit is unconfirmed; inspect it before retrying.');
    state.edit = { state: 'confirmed', body }; persist();
  });
}
