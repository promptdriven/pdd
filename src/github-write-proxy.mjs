import { githubAppRunner } from './github-app.mjs';
// Implements prompts/cli/github-write-proxy.prompt.md.
import * as nativeFs from 'node:fs';
import { spawn } from 'node:child_process';
import { constants as osConstants } from 'node:os';
import { createHash } from 'node:crypto';
import { join, delimiter } from 'node:path';
import { fileURLToPath } from 'node:url';
import { setTimeout as delay } from 'node:timers/promises';
import { countGithubCalls, githubCall, githubLedger, githubReply, githubRepository, githubStateRoot } from './github-calls.mjs';
import { githubWriteBudget, githubWriteLock } from './github-writes.mjs';

const self = fileURLToPath(import.meta.url), STATUS = '<!-- pdd:autopilot:status -->';
const hash = text => createHash('sha256').update(text).digest('hex').slice(0, 20);
const activeFile = (root, host) => join(root, 'github-writes', `active-${hash(host)}.json`);
const option = (args, ...names) => {
  for (let i=0;i<args.length;i++) for (const name of names) {
    if(args[i]===name) return args[i+1];
    if(args[i].startsWith(`${name}=`)) return args[i].slice(name.length+1);
  }
};
const targetHost = (args,options,env) => {
  const endpoint=githubCall(args).endpoint;
  if(/^https:\/\//i.test(endpoint)) { const host=new URL(endpoint).hostname; return host==='api.github.com'?'github.com':host; }
  return option(args,'--hostname') || options?.env?.GH_HOST || env.GH_HOST || 'github.com';
};
export function githubOriginalExecutable({env=process.env,fs=nativeFs}={}) {
  for(const folder of (env.PATH??'').split(delimiter)) {
    if(folder.includes('/github-bin/') || folder.endsWith('/bin/github-app')) continue;
    const file=join(folder,'gh');
    try { fs.accessSync(file,nativeFs.constants.X_OK); if(fs.statSync(file).isFile()) return file; } catch { /* Next PATH entry. */ }
  }
  return null;
}
function valueOf(result) {
  const reply = githubReply(result?.stdout);
  if ((result?.code ?? 0) !== 0 || reply && (reply.status < 200 || reply.status >= 300)) throw Object.assign(Error('GitHub request failed'), result);
  return JSON.parse(reply ? reply.body : result.stdout);
}
function knownIdentity({ root, host, fs }) {
  try { const value = JSON.parse(fs.readFileSync(activeFile(root, host), 'utf8')); return typeof value.identity === 'string' && value.identity ? value.identity : 'unknown'; } catch { return 'unknown'; }
}
export function githubWriteUsage({ root, env = process.env, fs = nativeFs, now = Date.now, machine } = {}) {
  root ??= env.PDD_GITHUB_ROOT || githubStateRoot(env);
  const host = env.GH_HOST || 'github.com', identity = knownIdentity({ root, host, fs });
  return githubWriteBudget({ root, host, identity, fs, now, machine }).usage();
}
export function githubWriteUsages({ root, env = process.env, fs = nativeFs, now = Date.now, machine } = {}) {
  root ??= env.PDD_GITHUB_ROOT || githubStateRoot(env);
  let names = [];
  try { names = fs.readdirSync(join(root, 'github-writes')).filter(name => /^(?:[0-9a-f]{20}|cooldown-[0-9a-f]{20}-[0-9a-f-]+)\.json$/.test(name)); } catch { /* No write state yet. */ }
  const usages = [], seen = new Set();
  for (const name of names) {
    try {
      const value = JSON.parse(fs.readFileSync(join(root, 'github-writes', name), 'utf8'));
      const key = `${value.host}/${value.identity}`;
      if (typeof value.identity === 'string' && typeof value.host === 'string' && !seen.has(key)) {
        usages.push(githubWriteBudget({ root, identity:value.identity, host:value.host, fs, now, machine }).usage()); seen.add(key);
      }
    } catch { /* One broken identity must not hide other identities. */ }
  }
  return usages.length ? usages.sort((a,b) => `${a.host}/${a.identity}`.localeCompare(`${b.host}/${b.identity}`)) : [githubWriteUsage({root,env,fs,now,machine})];
}
export function observeGithubWriteClaims({ root, env = process.env, fs = nativeFs, now = Date.now, machine, repository, claims }) {
  const host = env.GH_HOST || 'github.com', identity = knownIdentity({ root, host, fs });
  githubWriteBudget({ root, host, identity, fs, now, machine }).observeClaims(repository, claims);
  // Claims may have arrived before the first write resolved identity. The unknown
  // bucket also keeps the observations so a later identity inherits them.
  if (identity !== 'unknown') githubWriteBudget({ root, host, identity: 'unknown', fs, now, machine }).observeClaims(repository, claims);
}

export function githubWriteRunner(exec, { root, env = process.env, fs = nativeFs, now = Date.now, identity, machine, ledger } = {}) {
  root ??= env.PDD_GITHUB_ROOT || githubStateRoot(env);
  const identities = new Map();
  const resolveBudget = async (args, options) => {
    const host = targetHost(args,options,env).toLowerCase();
    if (!identities.has(host)) identities.set(host, (async () => {
      let login = typeof identity === 'function' ? await identity() : identity;
      if (!login) {
        try {
          const result = await exec('gh', ['auth', 'status', '--active', '--json', 'hosts'], { ...options, env: { ...(options?.env ?? env), PDD_GITHUB_COUNTED: '1' } });
          login = result.githubIdentity || valueOf(result).hosts?.[host]?.find(x => x.active === true)?.login;
        } catch (error) { login = error.githubIdentity; }
        if (!login) try { login = valueOf(await exec('gh', ['api', '--hostname', host, 'user'], { ...options, env: { ...(options?.env ?? env), PDD_GITHUB_COUNTED: '1' } })).login; } catch { /* Unknown identities share a conservative bucket. */ }
      }
      login = typeof login === 'string' && login ? login.toLowerCase() : 'unknown';
      fs.mkdirSync(join(root, 'github-writes'), { recursive: true, mode: 0o700 });
      fs.writeFileSync(activeFile(root, host), JSON.stringify({ identity: login }), { mode: 0o600 });
      return githubWriteBudget({ root, host, identity: login, fs, now, machine });
    })());
    return identities.get(host);
  };
  const counted = countGithubCalls(exec, { ledger, now, writes: resolveBudget, env });
  const api = async (method, endpoint, body, options) => counted('gh', ['api', '--hostname', options?.env?.GH_HOST || env.GH_HOST || 'github.com', '--include', '--method', method, endpoint, ...(body ? ['--input', '-'] : [])], { ...options, ...(body ? { input: JSON.stringify(body) } : {}) });
  return async (file, args, options = {}) => {
    if (file !== 'gh') return exec(file, args, options);
    const call = githubCall(args), repository = githubRepository(args) ?? options.repository;
    const host = targetHost(args,options,env);
    const transportOptions = { ...options, env: { ...(options.env ?? env), GH_HOST: host } };
    let body;
    try { body = JSON.parse(options.input ?? '{}').body; } catch { /* Not a JSON comment. */ }
    for (let i = 0; i < args.length; i++) if (args[i].startsWith('body=')) body = args[i].slice(5);
    if (call.method === 'POST' && args.includes('--include') && !args.some(x => ['--jq','-q','--template','-t'].includes(x) || /^--(?:jq|template)=/.test(x)) && /^repos\/[^/]+\/[^/]+\/issues\/\d+\/comments$/.test(call.endpoint) && typeof body === 'string' && body.includes(STATUS)) {
      const budget = await resolveBudget(args, options), login = budget.usage().identity;
      if (login === 'unknown') throw Object.assign(Error('GitHub status comment needs a known identity'), { code: 'github_identity_unknown' });
      const statusPath = call.endpoint.toLowerCase().replace(/\/0*(\d+)\/comments$/, '/$1/comments');
      const directory = join(root, 'github-writes', `status-${hash(`${host.toLowerCase()}/${login}/${statusPath}`)}.lock`);
      const deadline = Date.now() + 1000;
      let release;
      while (!release) {
        try { release = githubWriteLock({ directory, fs }); }
        catch (error) {
          if (error.code !== 'github_write_lock_busy' || Date.now() >= deadline) throw Object.assign(Error('GitHub status reconciliation deferred'), { code: 'github_write_budget', retryAt: now() + 60_000 });
          await delay(10);
        }
      }
      try {
        let next = `${call.endpoint}?per_page=100`, found;
        while (next) {
          const result = await api('GET', next, undefined, transportOptions), rows = valueOf(result);
          if (!Array.isArray(rows)) throw Error('GitHub comments unavailable');
          found ??= rows.find(row => row.user?.login?.toLowerCase() === login && row.body?.includes(STATUS));
          const link = githubReply(result.stdout)?.link;
          const target = /<([^>]+)>;\s*rel="next"/.exec(link ?? '')?.[1];
          if (target) { const url = new URL(target); if (url.hostname !== (host === 'github.com' ? 'api.github.com' : host)) throw Error('Invalid GitHub pagination host'); next = url.pathname.slice(1) + url.search; } else next = null;
        }
        if (found?.body === body) return { code: 0, stdout: `HTTP/2.0 200 OK\r\n\r\n${JSON.stringify(found)}`, stderr: '' };
        return await api(found ? 'PATCH' : 'POST', found ? `repos/${repository}/issues/comments/${found.id}` : call.endpoint, { body }, transportOptions);
      } finally { release(); }
    }
    // Combine label edits with atomic add/remove operations, preserving other writers. A claim
    // remove/add of the same label must retain its two separate era events.
    if (args[0] === 'issue' && args[1] === 'edit' && /^\d+$/.test(args[2] ?? '') && repository) {
      const add = [], remove = []; let labelsOnly = args.length > 3;
      for (let i = 3; i < args.length; i += 2) {
        if (args[i] === '--add-label') add.push(...String(args[i + 1] ?? '').split(','));
        else if (args[i] === '--remove-label') remove.push(...String(args[i + 1] ?? '').split(','));
        else if (!['--repo', '-R'].includes(args[i])) labelsOnly = false;
      }
      if (labelsOnly && (add.length || remove.length) && !add.some(name => remove.includes(name))) {
        const endpoint = `repos/${repository}/issues/${args[2]}`, previous = await api('GET', endpoint, undefined, transportOptions), issue = valueOf(previous);
        if (!Array.isArray(issue.labels)) throw Error('GitHub labels unavailable');
        const before = issue.labels.map(x => typeof x === 'string' ? x : x.name);
        const adding = [...new Set(add)].filter(name => name && !before.includes(name)), removing = [...new Set(remove)].filter(name => before.includes(name));
        const output = () => ({code:0,stdout:`${issue.html_url}\n`,stderr:''});
        if (typeof issue.html_url !== 'string') throw Error('GitHub issue URL unavailable');
        if (!adding.length && !removing.length) return output();
        if (typeof issue.node_id !== 'string') throw Error('GitHub issue ID unavailable');
        const labels = new Map(); let page = 1;
        for (;;) {
          const rows = valueOf(await api('GET', `repos/${repository}/labels?per_page=100&page=${page++}`, undefined, transportOptions));
          if (!Array.isArray(rows)) throw Error('GitHub label IDs unavailable');
          for (const row of rows) labels.set(row.name, row.node_id);
          if (rows.length < 100) break;
        }
        const ids = names => names.map(name => { const id = labels.get(name); if (typeof id !== 'string' || !id) throw Error('GitHub label ID unavailable'); return id; });
        const variables = { subject: issue.node_id, ...(adding.length ? {add:ids(adding)} : {}), ...(removing.length ? {remove:ids(removing)} : {}) };
        const declarations = ['$subject:ID!', ...(adding.length ? ['$add:[ID!]!'] : []), ...(removing.length ? ['$remove:[ID!]!'] : [])];
        const query = `mutation(${declarations.join(',')}) { ${adding.length ? 'addLabelsToLabelable(input:{labelableId:$subject,labelIds:$add}) {clientMutationId}' : ''} ${removing.length ? 'removeLabelsFromLabelable(input:{labelableId:$subject,labelIds:$remove}) {clientMutationId}' : ''} }`;
        const result = await api('POST', 'graphql', { query, variables }, { ...transportOptions, repository });
        const value = valueOf(result);
        if (value.errors?.length) throw Object.assign(Error('GitHub label mutation unresolved'), result);
        return output();
      }
    }
    return counted(file, args, options);
  };
}

export function githubWriteEnvironment({ root, env = process.env, fs = nativeFs }) {
  const folder = join(root, 'github-bin', hash(self));
  fs.mkdirSync(folder, { recursive: true, mode: 0o700 });
  const wrapper = join(folder, 'gh');
  const source = `#!${process.execPath}\nimport(${JSON.stringify(new URL(import.meta.url).href)}).then(m => m.runGithubWriteProxy()).catch(() => { process.stderr.write('GitHub write transport unavailable\\n'); process.exitCode = 1; });\n`;
  let same = false; try { same = fs.readFileSync(wrapper,'utf8') === source; } catch { /* First launch. */ }
  if (!same) { const temp = `${wrapper}.${process.pid}.tmp`; fs.writeFileSync(temp,source,{mode:0o700}); fs.renameSync(temp,wrapper); }
  const original = (env.PATH ?? '').split(delimiter).filter(path => !path.includes(`${delimiter === ':' ? '/' : '\\'}github-bin${delimiter === ':' ? '/' : '\\'}`));
  return { PATH: [folder, ...original].join(delimiter), PDD_GITHUB_ROOT: root };
}

export async function runGithubWriteProxy() {
  const env = { ...process.env }, root = env.PDD_GITHUB_ROOT || githubStateRoot(env);
  env.PATH = (env.PATH ?? '').split(delimiter).filter(path => !path.includes('/github-bin/')).join(delimiter);
  const args = process.argv.slice(2);
  const children = new Set(), signals = ['SIGTERM', 'SIGINT', 'SIGHUP'];
  let cancelling;
  const finishCancellation = () => {
    for (const signal of signals) process.removeListener(signal, handlers[signal]);
    process.kill(process.pid, cancelling);
  };
  const handlers = Object.fromEntries(signals.map(signal => [signal, () => {
    if (cancelling) return;
    cancelling = signal;
    for (const child of children) child.kill(signal);
    if (!children.size) finishCancellation();
  }]));
  for (const signal of signals) process.on(signal, handlers[signal]);
  const raw = (file, words, options = {}) => new Promise((resolveResult, reject) => {
    if (cancelling) { reject(Error('GitHub command cancelled')); return; }
    const child = spawn(file, words, { env: { ...env, ...options.env }, stdio: ['pipe', 'pipe', 'pipe'] });
    children.add(child);
    child.once('close', () => { children.delete(child); if (cancelling && !children.size) finishCancellation(); });
    let stdout = '', stderr = '';
    child.stdout.on('data', data => { stdout += data; }); child.stderr.on('data', data => { stderr += data; });
    child.on('error', reject); child.on('close', (code, signal) => resolveResult({ code: code ?? (128 + (osConstants.signals[signal] ?? 0)), stdout, stderr }));
    child.stdin.on('error', () => {}); child.stdin.end(options.input);
  });
  try {
  let input = '';
  if (!process.stdin.isTTY) for await (const part of process.stdin) input += part;
  if (env.PDD_GITHUB_COUNTED === '1') {
    const result = await raw('gh', args, { input }); process.stdout.write(result.stdout); process.stderr.write(result.stderr); process.exitCode = result.code; return;
  }
  const repository = githubRepository(args), ledger = repository ? githubLedger({ root, repository }) : null;
  try {
    const runner = githubWriteRunner(githubAppRunner(raw, { env }), { root, env, ledger });
    const result = await runner('gh', args, { input });
    process.stdout.write(result.stdout); process.stderr.write(result.stderr); process.exitCode = result.code;
  } catch (error) { process.stderr.write(`${error.message}\n`); process.exitCode = 1; }
  } finally { if (!cancelling) for (const signal of signals) process.removeListener(signal, handlers[signal]); }
}
