// Generated from prompts/cli/workflow-bug-cause.prompt.md (sha256: ddcabe16535aed00800d17c10e92d7fb25f83d4e819696e89b5e10ebf61e67d0).
import { execFile } from 'node:child_process';
import { lstatSync, readFileSync, realpathSync } from 'node:fs';
import { join } from 'node:path';

const problem = (code, message) => Object.assign(Error(message), { code });
const invalid = message => problem('bug-cause-invalid', message);
const positive = n => Number.isSafeInteger(n) && n > 0;
const safePath = path => typeof path === 'string' && path.length > 0 && !path.includes('\\') && !/[\x00-\x1f\x7f]/.test(path)
  && !path.startsWith('/') && !/^[A-Za-z]:/.test(path) && path.split('/').every(p => p && p !== '.' && p !== '..' && p !== '.git');
const parseApi = text => JSON.parse(text, (key, value, context) => key === 'id' && typeof value === 'number' ? context.source : value);
const nativeExec = (file, args, options) => new Promise((resolve, reject) => {
  const child = execFile(file, args, { cwd: options.cwd, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024 }, (error, stdout, stderr) => error ? reject(error) : resolve({ stdout, stderr }));
  child.stdin.on('error', () => {}); child.stdin.end(options.input ?? '');
});
function nativePorts(root, supplied) {
  const execute = supplied.execFile ?? nativeExec;
  const command = async (file, args, input) => {
    const out = await execute(file, args, { cwd: root, ...(input === undefined ? {} : { input }) });
    if ((out.code ?? out.exitCode ?? 0) !== 0) throw Error(`${file} failed (${out.code ?? out.exitCode})`);
    return String(out.stdout ?? '');
  };
  const api = async (endpoint, payload) => parseApi(await command('gh', ['api', endpoint, ...(payload === undefined ? [] : ['--method', 'POST', '--input', '-'])], payload));
  const pages = async endpoint => {
    const rows = [];
    for (let page = 1; ; page++) {
      const batch = await api(`${endpoint}?per_page=100&page=${page}`);
      if (!Array.isArray(batch)) throw Error('GitHub list unavailable');
      rows.push(...batch); if (batch.length < 100) return rows;
    }
  };
  const identity = issue => {
    if (!/^[1-9]\d*$/.test(String(issue.id))) throw Error('GitHub issue identity unavailable');
    return String(issue.id);
  };
  return {
    code: { read: async ({ path }) => {
      if (!safePath(path)) throw invalid('Unsafe code evidence path.');
      const canonical = realpathSync(root); let cursor = canonical;
      for (const part of path.split('/')) { cursor = join(cursor, part); if (lstatSync(cursor).isSymbolicLink()) throw invalid('Code evidence cannot use symlinks.'); }
      if (!lstatSync(cursor).isFile()) throw invalid('Code evidence must be a regular file.');
      await command('git', ['--literal-pathspecs', 'ls-files', '--error-unmatch', '--', path]);
      return { content: readFileSync(cursor, 'utf8') };
    } },
    issues: { read: async ({ repository, number }) => ({ json: await command('gh', ['api', `repos/${repository}/issues/${number}`]) }) },
    links: { ensure: async ({ repository, number, target, kind }) => {
      const subject = `repos/${repository}/issues/${number}`;
      if (kind === 'duplicate') {
        const body = `Duplicate of #${target}`;
        const exists = async () => (await pages(`${subject}/comments`)).some(row => row.body === body);
        if (await exists()) return { ok: true };
        await api(`${subject}/comments`, JSON.stringify({ body }));
        if (!await exists()) throw Error('Duplicate comment not confirmed.');
      } else {
        const endpoint = kind === 'sub-issue' ? `repos/${repository}/issues/${target}/sub_issues` : `${subject}/dependencies/blocked_by`;
        const child = kind === 'sub-issue' ? number : target;
        const id = identity(await api(`repos/${repository}/issues/${child}`));
        const exists = async () => (await pages(endpoint)).some(row => String(row.id) === id);
        if (await exists()) return { ok: true };
        await api(endpoint, `{"${kind === 'sub-issue' ? 'sub_issue_id' : 'issue_id'}":${id}}`);
        if (!await exists()) throw Error('Issue link not confirmed.');
      }
      return { ok: true };
    } }
  };
}

export async function recordBugCause({ text, repository, number, root }, supplied = {}) {
  const rows = String(text ?? '').split(/\r?\n/), causes = rows.filter(row => row.startsWith('Cause:')), relations = rows.filter(row => row.startsWith('Relations:'));
  if (!causes.length && !relations.length) return { json: '' };
  if (!/^[\w.-]+\/[\w.-]+$/.test(repository) || !positive(number) || causes.length !== 1 || relations.length !== 1) throw invalid('Supply one Cause line and one Relations line for this issue.');
  const match = /^Cause: (.+?)#([^·#]+?) · Flaw: (.+?) · Class: (.+)$/.exec(causes[0]);
  if (!match || match.slice(1).some(value => !value.trim())) throw invalid('Cause must name file#function, Flaw and Class.');
  const [, file, fn, flaw, className] = match.map(value => value.trim());
  const p = { ...nativePorts(root, supplied), ...supplied };
  const readCode = async path => {
    if (!safePath(path)) throw invalid('Unsafe code evidence path.');
    try { const result = await p.code.read({ root, path }); if (typeof result?.content !== 'string') throw Error(); return result.content; }
    catch (error) { if (error.code === 'bug-cause-invalid') throw error; throw problem('bug-cause-unavailable', `Code evidence unavailable: ${path}`); }
  };
  if (!(await readCode(file)).includes(fn)) throw invalid('The named function does not occur in the cause file.');
  let selected;
  try { selected = JSON.parse(relations[0].slice('Relations:'.length)); } catch { throw invalid('Relations must be a JSON array.'); }
  if (!Array.isArray(selected)) throw invalid('Relations must be a JSON array.');
  const seen = new Set(), allowed = { needs: ['blocked by'], 'same cause': ['none', 'blocked by'], 'same class': ['none', 'sub-issue'], duplicate: ['duplicate'], related: ['none'] };
  for (const row of selected) {
    if (!row || typeof row !== 'object' || Array.isArray(row) || Object.keys(row).sort().join(',') !== 'issue,kind,link,quote,source'
      || !positive(row.issue) || row.issue === number || seen.has(row.issue) || typeof row.kind !== 'string' || !Object.hasOwn(allowed,row.kind) || !allowed[row.kind].includes(row.link)
      || typeof row.quote !== 'string' || !row.quote.trim() || row.quote.length > 1000 || typeof row.source !== 'string') throw invalid('Invalid, repeated or incompatible issue relation.');
    seen.add(row.issue);
    let target;
    try { target = parseApi((await p.issues.read({ repository, number: row.issue })).json); }
    catch { throw problem('bug-cause-unavailable', `Issue evidence unavailable: #${row.issue}`); }
    if (target?.number !== row.issue || target.state !== 'open' || Object.hasOwn(target, 'pull_request')) throw invalid('Relation target must be another open issue.');
    if (row.link === 'sub-issue' && target.title !== `Class: ${className}`) throw invalid('Sub-issue target must be the named Class parent.');
    let evidence;
    if (row.source === `issue:${row.issue}`) evidence = [target.title, target.body].filter(x => typeof x === 'string');
    else if (row.source.startsWith('code:')) evidence = [await readCode(row.source.slice(5))];
    else throw invalid('Evidence must name the target issue or a code file.');
    if (!evidence.some(value => value.includes(row.quote))) throw invalid(`Quote not found for #${row.issue}.`);
  }
  for (const row of selected.filter(row => row.link !== 'none')) {
    try { if (!(await p.links.ensure({ repository, number, target: row.issue, kind: row.link }))?.ok) throw Error(); }
    catch { throw problem('bug-cause-link-failed', `Could not confirm ${row.link} link to #${row.issue}; inspect GitHub and retry.`); }
  }
  return { json: JSON.stringify({ file, function: fn, flaw, class: className, relations: selected,
    causeLine: `Cause: ${file}#${fn} · Flaw: ${flaw} · Class: ${className}`, relationsLine: `Relations: ${JSON.stringify(selected)}` }) };
}
