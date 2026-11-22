// Generated from prompts/cli/product.prompt.md.
// Layer 1 core: GitHub repository/issue lookup, local binding cache, base-source views, and read-only local run discovery (ZERO legacy workflow imports).
import { execFile as execute } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { closeSync, existsSync, fstatSync, lstatSync, openSync, readFileSync, realpathSync, unlinkSync, writeFileSync } from 'node:fs';
import { mkdir, mkdtemp, readFile, readdir, rename, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, isAbsolute, join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { gitContext } from '../../shared/git-context.mjs';
import { githubOriginRepository, sameRepo } from '../../shared/github-repo.mjs';
import { causeText } from '../../shared/safe-read.mjs';
import { githubReply, nativeGithubCounter } from '../../github-calls.mjs';
import { runtimeClientSlice } from '../../runtime-seam.mjs';
import { invalid } from './markdown-utils.mjs';
import { marker, ownProductMarker, productPrefix } from './pr-matching.mjs';

const { createSavedStoryEvidenceReader } = runtimeClientSlice();
const ordinary = promisify(execute);
const REPO_NAME_RE = /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/;
const PAGE_SIZE = 10;

const canonicalRoot = cwd => { try { return realpathSync(cwd); } catch { return resolve(cwd); } };
const parseJson = text => { try { return JSON.parse(text); } catch { invalid('GitHub returned unreadable JSON.'); } };
const nonControlText = value => typeof value === 'string' && value.length > 0 && !/[\u0000-\u001f\u007f]/u.test(value);

export async function command(p, cwd, file, args, allowAbsent = false) {
  let response;
  try { response = await p.execFile(file, args, { cwd }); }
  catch (error) {
    if (allowAbsent && Number.isInteger(error.code) && error.code === 1) return null;
    throw Error(`Could not run ${file}: ${causeText(error.message)}`);
  }
  if (!response || typeof response.stdout !== 'string') throw Error(`Invalid ${file} response.`);
  if (response.code !== undefined && response.code !== 0) {
    if (allowAbsent && response.code === 1) return null;
    throw Error(`${file} failed: ${causeText(response.stderr || response.code)}`);
  }
  return response.stdout;
}

export async function resolveProductRepository({ cwd } = {}, ports = {}) {
  if (!nonControlText(cwd)) throw Error('Git repository cwd is required to resolve product repository.');
  const execFile = ports.execFile ?? nativeGithubCounter((file, args, options) => ordinary(file, args, { ...options, encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 }));
  const p = { execFile };
  const remote = (await command(p, cwd, 'git', ['remote', 'get-url', 'origin'])).trim();
  const repository = githubOriginRepository(remote);
  if (!repository || !REPO_NAME_RE.test(repository)) {
    throw Error('Git origin remote is not a standard GitHub repository URL. Point origin at https://github.com/OWNER/REPO or git@github.com:OWNER/REPO.git, then rerun pdd product.');
  }
  const actual = parseJson(await command(p, cwd, 'gh', ['repo', 'view', repository, '--json', 'nameWithOwner,defaultBranchRef,url']));
  if (
    !nonControlText(actual?.nameWithOwner) || !REPO_NAME_RE.test(actual.nameWithOwner)
    || !sameRepo(actual.nameWithOwner, repository)
    || !nonControlText(actual.defaultBranchRef?.name)
    || actual.url !== `https://github.com/${actual.nameWithOwner}`
  ) {
    throw Error(`GitHub repository metadata for ${repository} did not match origin. Verify gh auth and origin remote, then rerun pdd product.`);
  }
  return { repository: actual.nameWithOwner, defaultBranch: actual.defaultBranchRef.name };
}

export async function resolveBaseSha(p, { cwd, baseBranch }) {
  if (typeof baseBranch !== 'string' || !baseBranch.trim()) return null;
  for (const ref of [`refs/heads/${baseBranch}`, `refs/remotes/origin/${baseBranch}`]) {
    const found = await command(p, cwd, 'git', ['rev-parse', '--verify', '--quiet', '--end-of-options', `${ref}^{commit}`], true);
    if (found !== null) {
      const sha = found.trim();
      if (/^[0-9a-f]{40,64}$/.test(sha)) return sha;
    }
  }
  return null;
}

export async function openBaseSource({ cwd, baseBranch }, p, owned) {
  const listing = await command(p, cwd, 'git', ['worktree', 'list', '--porcelain', '-z']);
  for (const record of listing.split('\0\0')) {
    const fields = record.split('\0'), branch = fields.find(field => field.startsWith('branch '));
    const path = fields.find(field => field.startsWith('worktree '))?.slice(9);
    if (branch === `branch refs/heads/${baseBranch}` && path && existsSync(path)) return { root: realpathSync(path), handle: null };
  }
  let sha = null;
  for (const ref of [`refs/heads/${baseBranch}`, `refs/remotes/origin/${baseBranch}`]) {
    const found = await command(p, cwd, 'git', ['rev-parse', '--verify', '--quiet', '--end-of-options', `${ref}^{commit}`], true);
    if (found !== null) { sha = found.trim(); break; }
  }
  if (sha === null) return { root: null, handle: null };
  if (!/^[0-9a-f]{40}$/.test(sha)) throw Error('The base commit could not be identified.');
  const directory = await mkdtemp(join(tmpdir(), 'pdd-base-source-'));
  const env = { ...process.env, GIT_CONFIG_NOSYSTEM: '1', GIT_CONFIG_GLOBAL: '/dev/null', GIT_CONFIG_SYSTEM: '/dev/null', GIT_TERMINAL_PROMPT: '0', GIT_ATTR_NOSYSTEM: '1' };
  for (const key of Object.keys(env)) {
    if (/^GIT_(?:CONFIG_(?:COUNT|KEY_\d+|VALUE_\d+|PARAMETERS)|DIR|WORK_TREE|INDEX_FILE|OBJECT_DIRECTORY|ALTERNATE_OBJECT_DIRECTORIES|COMMON_DIR|TEMPLATE_DIR)$/.test(key)) delete env[key];
  }
  const isolated = { execFile: (file, args, options) => p.execFile(file, args, { ...options, env }) };
  try {
    await command(isolated, cwd, 'git', ['-c', 'core.hooksPath=/dev/null', 'clone', '--shared', '--no-checkout', '--template=', '--quiet', '--', realpathSync(cwd), directory]);
    await command(isolated, directory, 'git', ['-c', 'core.hooksPath=/dev/null', 'checkout', '--detach', '--quiet', sha]);
    const handle = randomUUID(); owned.set(handle, directory); return { root: directory, handle };
  } catch (error) { await rm(directory, { recursive: true, force: true }); throw error; }
}

export async function basePlan(p, { cwd, baseBranch }) {
  if (p.planOnBase) { const value = await p.planOnBase({ cwd, baseBranch }); return value === true || value?.present === true; }
  for (const ref of [`refs/remotes/origin/${baseBranch}`, `refs/heads/${baseBranch}`]) {
    const present = await command(p, cwd, 'git', ['rev-parse', '--verify', '--quiet', `${ref}^{commit}`], true);
    if (present === null) continue;
    return (await command(p, cwd, 'git', ['ls-tree', '--name-only', ref, '--', 'product/plan.md'])).trim() === 'product/plan.md';
  }
  return false;
}

async function listLocalRuns({ cwd }, { execFile }) {
  const ctx = await gitContext(cwd, { execFile });
  if (!ctx?.commonDir) return [];
  const runsRoot = join(ctx.commonDir, 'pdd', 'runs');
  let names;
  try { names = await readdir(runsRoot); } catch { return []; }
  const out = [];
  for (const name of names) {
    if (!/^[1-9][0-9]*$/.test(name)) continue;
    try {
      const runDir = join(runsRoot, name);
      const parsed = JSON.parse(await readFile(join(runDir, 'status.json'), 'utf8'));
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed) && Number.isSafeInteger(parsed.number)) {
        out.push({ ...parsed, runDir, commonDir: ctx.commonDir });
      }
    } catch {}
  }
  return out.sort((a, b) => a.number - b.number);
}

export function portsFor(given = {}, { defaultStoryEvidence = async () => [] } = {}) {
  const execFile = given.execFile ?? nativeGithubCounter((file, args, options) => ordinary(file, args, { ...options, encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 }));
  const p = {
    readFile: path => readFile(path, 'utf8'),
    listRuns: input => listLocalRuns(input, { execFile }),
    storyEvidence: defaultStoryEvidence,
    savedStoryEvidence: createSavedStoryEvidenceReader(),
    resolveRepository: input => resolveProductRepository(input, { execFile }),
    ...given,
    execFile,
    _customReadFile: typeof given.readFile === 'function',
    _customExecFile: typeof given.execFile === 'function',
  };
  p.issuePage ??= async ({ cwd, repository, marker: qMarker, page, perPage }) => {
    const quoted = qMarker.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
    const query = new URLSearchParams({ q: `repo:${repository} is:issue in:body "${quoted}"`, sort: 'created', order: 'asc', page, per_page: perPage });
    return parseJson(await command(p, cwd, 'gh', ['api', `search/issues?${query}`, '--jq', '{items:[.items[]|{number,body,user:{login:.user.login},author_association,created_at,state}],total_count,incomplete_results}']));
  };
  p.timelinePage ??= async ({ cwd, repository, issue, page, perPage }) => parseJson(await command(p, cwd, 'gh',
    ['api', `repos/${repository}/issues/${issue}/timeline?per_page=${perPage}&page=${page}`, '--jq', '[.[]|{event,source:{issue:{pull_request:{html_url:.source.issue.pull_request.html_url}}}}]']));
  p.pullRequest ??= async ({ cwd, repository, number }) => parseJson(await command(p, cwd, 'gh', ['pr', 'view', String(number), '--repo', repository, '--json',
    'number,url,body,state,isDraft,updatedAt,headRefName,isCrossRepository,headRepository,headRepositoryOwner']));
  p.issueByNumber ??= async ({ cwd, repository, number }) => {
    let reply;
    try { reply = await p.execFile('gh', ['api', `repos/${repository}/issues/${number}`, '--include'], { cwd }); }
    catch (error) { reply = error; }
    const parsed = githubReply(reply?.stdout);
    if (parsed) {
      if (parsed.status >= 200 && parsed.status < 300) return parseJson(parsed.body);
      let value; try { value = JSON.parse(parsed.body); } catch {}
      return { status: parsed.status, message: typeof value?.message === 'string' ? value.message : 'GitHub issue lookup failed.' };
    }
    if ((reply?.code !== undefined && reply.code !== 0) || reply instanceof Error) throw Error('GitHub issue lookup is unavailable.');
    return parseJson(typeof reply?.stdout === 'string' ? reply.stdout : '');
  };
  p.now ??= async () => ({ milliseconds: Date.now() });
  const scopes = new Map();
  const statePath = input => {
    const key = `${input.cwd}\0${input.repository.toLowerCase()}`;
    if (!scopes.has(key)) scopes.set(key, (async () => {
      const common = (await command(p, input.cwd, 'git', ['rev-parse', '--git-common-dir'])).trim();
      if (!common) throw Error('The Git common directory is unavailable.');
      const directory = join(canonicalRoot(isAbsolute(common) ? common : resolve(input.cwd, common)), 'pdd', 'products');
      const name = createHash('sha256').update(input.repository.toLowerCase()).digest('hex');
      return join(directory, `${name}.json`);
    })());
    return scopes.get(key);
  };
  p.readProductState ??= async input => {
    const path = await statePath(input);
    try { return { json: await readFile(path, 'utf8') }; }
    catch (error) { if (error.code !== 'ENOENT') throw error; }
    let names; try { names = await readdir(dirname(path)); } catch (error) { if (error.code === 'ENOENT') return { json: null }; throw error; }
    const merged = { version: 2, repository: input.repository, bindings: [] };
    for (const name of names.filter(file => /^[0-9a-f]{64}\.json$/.test(file))) {
      let old; try { old = JSON.parse(await readFile(join(dirname(path), name), 'utf8')); } catch { continue; }
      if (old?.version !== 1 || !sameRepo(old.repository, input.repository) || typeof old.productRoot !== 'string' || !Array.isArray(old.bindings)) continue;
      const legacyKey = createHash('sha256').update(`${old.repository.toLowerCase()}\0${canonicalRoot(old.productRoot)}`).digest('hex');
      if (name !== `${legacyKey}.json`) continue;
      for (const row of old.bindings) if (!merged.bindings.some(saved => saved.run === row.run && saved.issue === row.issue)) merged.bindings.push(row);
      if (old.search && (!merged.search || old.search.at > merged.search.at)) merged.search = old.search;
    }
    return { json: merged.bindings.length || merged.search ? JSON.stringify({ ...merged, version: 1, productRoot: input.cwd }) : null };
  };
  p.writeProductState ??= async input => {
    const path = await statePath(input), temporary = `${path}.${randomUUID()}.tmp`;
    await mkdir(dirname(path), { recursive: true });
    try { await writeFile(temporary, input.json, { flag: 'wx', mode: 0o600 }); await rename(temporary, path); }
    finally { await rm(temporary, { force: true }); }
    return {};
  };
  const locks = new Map();
  const observedLock = path => ({ stat: lstatSync(path), content: readFileSync(path, 'utf8') });
  const removeObservedLock = (path, observed) => {
    try {
      const current = observedLock(path);
      if (current.stat.dev === observed.stat.dev && current.stat.ino === observed.stat.ino && current.content === observed.content) unlinkSync(path);
    } catch (error) { if (error.code !== 'ENOENT') throw error; }
  };
  p.lockProductState ??= async input => {
    const path = `${await statePath(input)}.lock`, until = Date.now() + 10000;
    try {
      await mkdir(dirname(path), { recursive: true });
      for (;;) {
        try {
          const file = openSync(path, 'wx', 0o600), handle = randomUUID();
          const content = JSON.stringify({ pid: process.pid, token: handle });
          try { writeFileSync(file, content); locks.set(handle, { path, stat: fstatSync(file), content }); }
          finally { closeSync(file); }
          return { handle };
        } catch (error) {
          if (error.code !== 'EEXIST') throw error;
          let observed;
          try { observed = observedLock(path); } catch (err) { if (err.code === 'ENOENT') continue; throw err; }
          let owner; try { owner = JSON.parse(observed.content); } catch {}
          let dead = false;
          if (Number.isSafeInteger(owner?.pid) && owner.pid > 0) {
            try { process.kill(owner.pid, 0); } catch (err) { dead = err.code === 'ESRCH'; }
          }
          if (dead || Date.now() - observed.stat.mtimeMs > 30000) { removeObservedLock(path, observed); continue; }
          if (Date.now() >= until) throw Error('Product state is busy; try the command again.');
          await new Promise(resolveTimer => setTimeout(resolveTimer, 5));
        }
      }
    } catch (error) { throw Error(`Product state lock ${path}: ${error.message}`); }
  };
  p.unlockProductState ??= async ({ handle }) => {
    const lock = locks.get(handle); if (!lock) throw Error('Product state lock is not owned by this command.');
    try { removeObservedLock(lock.path, lock); }
    catch (error) { throw Error(`Product state lock ${lock.path}: ${error.message}`); }
    finally { locks.delete(handle); }
    return {};
  };
  p.currentActor ??= async ({ cwd }) => parseJson(await command(p, cwd, 'gh', ['api', 'user', '--jq', '{login}']));
  p.reopenIssue ??= async ({ cwd, repository, number }) => {
    await command(p, cwd, 'gh', ['api', `repos/${repository}/issues/${number}`, '-X', 'PATCH', '-f', 'state=open']);
    return {};
  };
  const owned = new Map();
  p.openBaseSource ??= input => openBaseSource(input, p, owned);
  p.closeBaseSource ??= async ({ handle }) => {
    const directory = owned.get(handle);
    if (!directory) throw Error('The base-source view is not owned by this command.');
    await rm(directory, { recursive: true, force: true }); owned.delete(handle); return {};
  };
  return p;
}

const compareIssues = (a, b, localA, localB) => Number(!!localB) - Number(!!localA)
  || (Date.parse(a.created_at) || 0) - (Date.parse(b.created_at) || 0) || a.number - b.number;
const unverifiedFallback = (failed, repair) => failed.find(row => !row.confirmed) ?? (repair ? null : failed[0]) ?? null;

export async function issueLookup(p, cwd, repository, localRuns, warning) {
  const scope = { cwd, repository }, migration = Symbol('legacy-state');
  const rawIssue = issue => issue && Number.isSafeInteger(issue.number) && issue.number > 0 && typeof issue.body === 'string';
  const decode = reply => {
    if (!reply || !(reply.json === null || typeof reply.json === 'string')) invalid('Invalid local product state.');
    if (reply.json === null) return { version: 2, repository, bindings: [] };
    let value; try { value = JSON.parse(reply.json); } catch { invalid('Invalid local product state JSON.'); }
    if (!value || ![1, 2].includes(value.version) || !Array.isArray(value.bindings)
      || value.bindings.some(row => !row || typeof row.run !== 'string' || !row.run || !Number.isSafeInteger(row.issue) || row.issue < 1)
      || new Set(value.bindings.map(row => `${row.run}\0${row.issue}`)).size !== value.bindings.length) {
      invalid('Invalid local product bindings.');
    }
    if (!sameRepo(value.repository, repository)) {
      if (value.bindings.length) invalid('Foreign local product bindings.');
      return { version: 2, repository, bindings: [] };
    }
    return { version: 2, repository, bindings: value.bindings, ...(value.search ? { search: value.search } : {}), [migration]: value.version === 1 };
  };
  let state = decode(await p.readProductState(scope));
  const time = (await p.now()).milliseconds;
  if (!Number.isFinite(time)) invalid('Invalid product clock.');
  const mutate = async ({ upsert, remove, search }) => {
    const lock = await p.lockProductState(scope);
    if (!lock || typeof lock.handle !== 'string' || !lock.handle) invalid('Invalid product state lock.');
    try {
      const latest = decode(await p.readProductState(scope));
      const commitTime = search ? (await p.now()).milliseconds : time;
      if (!Number.isFinite(commitTime)) invalid('Invalid product clock.');
      if (remove) latest.bindings = latest.bindings.filter(row => row.run !== remove.run || row.issue !== remove.issue);
      if (upsert) latest.bindings = [...latest.bindings.filter(row => row.run !== upsert.run), upsert];
      if (search && (!Number.isFinite(latest.search?.at) || latest.search.at > commitTime || !Array.isArray(latest.search.items)
        || latest.search.items.length > 1000 || !latest.search.items.every(rawIssue) || search.at > latest.search.at)) latest.search = search;
      delete latest[migration];
      await p.writeProductState({ ...scope, json: JSON.stringify(latest) }); state = latest;
    } finally { await p.unlockProductState({ handle: lock.handle }); }
  };
  const repairWarnings = new Map();
  const bind = async (run, number) => {
    for (const diagnostic of repairWarnings.get(run) ?? []) {
      const index = warning.indexOf(diagnostic);
      if (index !== -1) warning[index] = diagnostic.slice(0, diagnostic.indexOf('. Run pdd product start')) + '.';
    }
    if (!state[migration] && state.bindings.filter(row => row.run === run).length === 1 && state.bindings.some(row => row.run === run && row.issue === number)) return;
    await mutate({ upsert: { run, issue: number } });
  };
  let actorPromise;
  const actor = () => actorPromise ??= Promise.resolve().then(() => p.currentActor({ cwd })).then(reply =>
    typeof reply?.login === 'string' && reply.login.trim() ? reply.login : null).catch(() => null);
  const trust = async issue => {
    if (['OWNER', 'MEMBER', 'COLLABORATOR'].includes(issue.author_association)) return 'trusted';
    const login = await actor();
    return login === null ? 'unavailable' : typeof issue.user?.login === 'string' && sameRepo(login, issue.user.login) ? 'trusted' : 'untrusted';
  };
  const valid = (issue, run, number) => issue && Number.isSafeInteger(issue.number) && issue.number > 0
    && (number === undefined || issue.number === number) && typeof issue.body === 'string' && !issue.pull_request
    && (!issue.repository_url || sameRepo(issue.repository_url, `https://api.github.com/repos/${repository}`))
    && ownProductMarker(issue.body, run);
  const localFor = (number, run) => localRuns.find(record => record.number === number
    && (record.workflow === undefined || record.workflow === 'feature')
    && (record.productMarker === undefined || record.productMarker === marker(run)));
  const direct = new Map(), excluded = new Map();
  const excludedFor = run => { if (!excluded.has(run)) excluded.set(run, new Set()); return excluded.get(run); };
  const failure = (run, number, reason, confirmed) => {
    const diagnostic = `Warning: Issue #${number} for ${run} is unverified: ${reason}. Run pdd product start ${run} to link it again.`;
    if (!repairWarnings.has(run)) repairWarnings.set(run, []);
    repairWarnings.get(run).push(diagnostic); warning.push(diagnostic);
    return { issue: { number }, unverified: true, reason, confirmed };
  };
  const inspect = async (run, number) => {
    let issue;
    try { issue = await p.issueByNumber({ ...scope, number }); }
    catch { return failure(run, number, 'GitHub issue lookup is unavailable', false); }
    let reason, confirmed = false;
    if (issue && Number.isInteger(issue.status) && typeof issue.message === 'string') {
      confirmed = issue.status === 404; reason = confirmed ? 'the saved issue is gone (404)' : `GitHub returned HTTP ${issue.status}`;
    } else if (!issue || issue.number !== number || typeof issue.body !== 'string') reason = 'GitHub returned a malformed issue';
    else if (!valid(issue, run, number)) { confirmed = true; reason = 'the issue repository or planned-run marker no longer matches'; }
    else {
      const verdict = await trust(issue);
      if (verdict === 'trusted') return { issue, local: localFor(number, run), unverified: false };
      confirmed = verdict === 'untrusted'; reason = confirmed ? 'the issue author is untrusted' : 'the authenticated account is unavailable';
    }
    if (confirmed) { excludedFor(run).add(number); await mutate({ remove: { run, issue: number } }); }
    return failure(run, number, reason, confirmed);
  };
  const bound = async (run, repair = false) => {
    if (direct.has(run)) return direct.get(run);
    const numbers = new Set([
      ...state.bindings.filter(row => row.run === run).map(row => row.issue),
      ...localRuns.filter(record => record.workflow === 'feature' && record.productMarker === marker(run)).map(record => record.number),
    ].filter(number => Number.isSafeInteger(number) && number > 0 && !excludedFor(run).has(number)));
    const candidates = [], failed = [];
    for (const number of numbers) { const candidate = await inspect(run, number); (candidate.unverified ? failed : candidates).push(candidate); }
    candidates.sort((a, b) => compareIssues(a.issue, b.issue, a.local, b.local));
    const result = candidates[0] ?? unverifiedFallback(failed, repair);
    if (result && !result.unverified) {
      if (candidates.length > 1) warning.push(`Warning: Multiple saved issues name ${run}; using issue #${result.issue.number}.`);
      await bind(run, result.issue.number);
    }
    direct.set(run, result); return result;
  };
  const cached = state.search;
  let snapshot = cached && Number.isFinite(cached.at) && time >= cached.at && time - cached.at < 60000
    && Array.isArray(cached.items) && cached.items.length <= 1000 && cached.items.every(rawIssue) ? cached.items : null;
  let fresh = false;
  const refresh = async () => {
    if (fresh) return;
    const found = new Map();
    for (let page = 1; ; page++) {
      const response = await p.issuePage({ ...scope, marker: productPrefix, page, perPage: PAGE_SIZE });
      if (!response || !Array.isArray(response.items) || response.items.length > PAGE_SIZE || !Number.isSafeInteger(response.total_count)
        || response.total_count < 0 || response.total_count > 1000 || response.incomplete_results !== false
        || response.items.length !== Math.min(PAGE_SIZE, Math.max(0, response.total_count - (page - 1) * PAGE_SIZE))) {
        invalid('GitHub returned an incomplete product issue search.');
      }
      for (const issue of response.items) { if (!rawIssue(issue)) invalid('GitHub returned an invalid product issue.'); found.set(issue.number, issue); }
      if (page * PAGE_SIZE >= response.total_count) break;
    }
    snapshot = [...found.values()]; fresh = true;
    await mutate({ search: { at: time, items: snapshot } });
  };
  const select = async (run, repair) => {
    const trusted = [], failed = [];
    for (const saved of snapshot) {
      if (excludedFor(run).has(saved.number) || typeof saved.body !== 'string' || !saved.body.includes(marker(run)) || saved.pull_request) continue;
      if (!ownProductMarker(saved.body, run)) { warning.push(`Warning: Ignored issue #${saved.number} with ambiguous planned-run markers.`); continue; }
      if (!fresh && await trust(saved) !== 'trusted') { warning.push(`Warning: Ignored untrusted issue #${saved.number} for ${run}.`); continue; }
      if (!fresh) {
        const candidate = await inspect(run, saved.number);
        if (candidate.unverified) { failed.push(candidate); continue; }
        trusted.push(candidate.issue);
      } else if (valid(saved, run, saved.number) && await trust(saved) === 'trusted') trusted.push(saved);
      else warning.push(`Warning: Ignored untrusted issue #${saved.number} for ${run}.`);
    }
    trusted.sort((a, b) => compareIssues(a, b, localFor(a.number, run), localFor(b.number, run)));
    if (trusted.length > 1) warning.push(`Warning: Multiple trusted issues name ${run}; using issue #${trusted[0].number}.`);
    if (!trusted.length) return unverifiedFallback(failed, repair);
    await bind(run, trusted[0].number);
    return { issue: trusted[0], local: localFor(trusted[0].number, run), unverified: false };
  };
  return {
    bound, bind,
    async find(run, create = false) {
      const known = await bound(run, create); if (known) return known;
      if (snapshot === null) await refresh();
      let selected = await select(run, create);
      if (!selected && create && !fresh) { await refresh(); selected = await select(run, create); }
      return selected;
    },
  };
}
