// Implements prompts/cli/autopilot-github.prompt.md.
import { execFile } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { resolveWorkflowRepository } from './workflow-github.mjs';
import { nativeGithubCounter } from './github-calls.mjs';

const MODES = ['off', 'observe', 'auto'];
const REFUSED = [403, 409, 422];
const PREFIX = 'pdd/autopilot-settings-';
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const success = status => Number.isInteger(status) && status >= 200 && status < 300;
const clean = value => String(value).replace(/[\x00-\x1f\x7f]/g, '');
const named = value => typeof value === 'string' && value.trim().length > 0;
const sameName = (a, b) => typeof a === 'string' && typeof b === 'string' && a.toLowerCase() === b.toLowerCase();
const unique = names => names.filter((name, index) => named(name) && names.findIndex(other => sameName(other, name)) === index);
// The same JSON value, whatever the key order.
const canonical = value => JSON.stringify(value ?? null, (key, item) => object(item)
  ? Object.fromEntries(Object.keys(item).sort().map(name => [name, item[name]])) : item);
const same = (a, b) => canonical(a) === canonical(b);
const modeOf = value => object(value) && MODES.includes(value.mode) ? value.mode : 'off';
const namesOf = value => object(value) && Array.isArray(value.trust) ? value.trust.filter(named) : [];
const trustKey = value => [...new Set(namesOf(value).map(name => name.toLowerCase()))].sort().join('\n');
// The effective settings that workers use: the mode and the trust names, ignoring case and order.
const sameSettings = (a, b) => modeOf(a) === modeOf(b) && trustKey(a) === trustKey(b);
const settings = value => `${modeOf(value)}, trust ${namesOf(value).map(clean).join(', ') || '(none)'}`;
const segments = branch => branch.split('/').map(encodeURIComponent).join('/');
const valid = ({ action, mode, names }) => action === 'mode' ? MODES.includes(mode)
  : ['trust', 'untrust'].includes(action) && Array.isArray(names) && names.length > 0 && names.every(named) && (action === 'trust' || names.length === 1);
class Stop extends Error {}
const RACE = Symbol('race');

const execute = (file, args, { cwd, input, env }) => new Promise((resolve, reject) => {
  const child = execFile(file, args, { cwd, env, encoding: 'utf8', shell: false, timeout: 15000, maxBuffer: 8 * 1024 * 1024 }, (error, stdout, stderr) => {
    if (error) { error.stdout = stdout; error.stderr = stderr; reject(error); }
    else resolve({ stdout, stderr });
  });
  child.stdin?.on('error', () => {});
  child.stdin?.end(input);
});
const parse = text => { try { return JSON.parse(text); } catch { return null; } };

// gh owns the sign-in; pdd adds no credentials.
function nativeGithub(root, exec) {
  return {
    repository: () => resolveWorkflowRepository({ cwd: root }, { execFile: exec }),
    async request({ method, path, body }) {
      const args = ['api', '--method', method, '-H', 'Accept: application/vnd.github+json', path, ...(body === undefined ? [] : ['--input', '-'])];
      try { return { status: 200, body: parse((await exec('gh', args, { cwd: root, input: body === undefined ? undefined : JSON.stringify(body) })).stdout) }; }
      catch (error) {
        const status = Number(/\(HTTP (\d{3})\)/.exec(String(error?.stderr ?? ''))?.[1]);
        if (!Number.isInteger(error?.code) || !status) throw Error('no HTTP answer');
        return { status, body: parse(error.stdout) };
      }
    },
  };
}

// The native runner records each gh call in the GitHub call ledger of its repository, as setup.
const counted = nativeGithubCounter(execute, { purpose: 'setup' });
async function context(cwd, ports) {
  const exec = ports.execFile ?? counted;
  const root = String((await exec('git', ['rev-parse', '--show-toplevel'], { cwd })).stdout).trim();
  if (!root) throw Error('no Git root');
  let config = {};
  try { config = JSON.parse(readFileSync(join(root, 'pdd.json'), 'utf8')); }
  catch (error) { if (error.code !== 'ENOENT') throw error; }
  if (!object(config)) throw Error('pdd.json is not an object');
  return { root, local: config.autopilot, github: ports.github ?? nativeGithub(root, exec) };
}

function repositoryReason(error) {
  if (error?.code === 'workflow_github_origin_invalid') return 'origin is not a github.com repository';
  if (error?.code === 'workflow_github_command_unavailable') return 'gh is missing or did not answer in time';
  if (/No such remote/i.test(String(error?.detail ?? ''))) return 'this repository has no origin remote';
  return 'GitHub could not be reached or gh is not signed in';
}
async function repositoryOf(github) {
  let repo;
  try { repo = await github.repository(); } catch (error) { throw new Stop(repositoryReason(error)); }
  if (!object(repo) || typeof repo.repository !== 'string' || typeof repo.defaultBranch !== 'string') throw new Stop('GitHub did not name the default branch');
  return repo;
}
async function ask(github, request) {
  try { return await github.request(request); }
  catch { throw new Stop('GitHub could not be reached or gh is not signed in'); }
}
async function readRemote(github, repository, branch) {
  const answer = await ask(github, { method: 'GET', path: `repos/${repository}/contents/pdd.json?ref=${encodeURIComponent(branch)}` });
  if (answer?.status === 404) return { sha: undefined, config: {}, text: undefined };
  if (!success(answer?.status)) throw new Stop(`GitHub did not send pdd.json (HTTP ${answer?.status})`);
  const file = answer.body;
  if (!object(file) || file.type !== 'file' || typeof file.sha !== 'string' || file.encoding !== 'base64' || typeof file.content !== 'string') throw new Stop(`GitHub did not send pdd.json of ${clean(branch)}`);
  const text = Buffer.from(file.content, 'base64').toString('utf8');
  const config = parse(text);
  if (!object(config)) throw new Stop(`pdd.json on ${clean(branch)} is not a JSON object; fix it on GitHub first`);
  return { sha: file.sha, config, text };
}
// The newest open settings PR comes first. Only branches of this repository count, never a fork.
async function settingsPulls(github, repository, base) {
  const found = [];
  for (let page = 1; page <= 10; page++) {
    const answer = await ask(github, { method: 'GET', path: `repos/${repository}/pulls?state=open&base=${encodeURIComponent(base)}&per_page=100&page=${page}` });
    if (!success(answer?.status) || !Array.isArray(answer.body)) throw new Stop(`GitHub did not list the open PRs (HTTP ${answer?.status})`);
    found.push(...answer.body.filter(pull => object(pull) && Number.isInteger(pull.number) && typeof pull.html_url === 'string'
      && typeof pull.head?.ref === 'string' && pull.head.ref.startsWith(PREFIX) && String(pull.head.repo?.full_name).toLowerCase() === repository.toLowerCase()));
    if (answer.body.length < 100) break;
  }
  return found.sort((a, b) => b.number - a.number);
}

// Only the change of this command; every other field keeps the GitHub value, also when this checkout is behind.
function apply({ action, mode, names }, value) {
  if (action === 'mode') {
    if (object(value) && value.mode === mode) return { value };
    return { value: object(value) ? { ...value, mode } : { mode, trust: [] }, message: `Set PDD Autopilot mode to ${clean(mode)}` };
  }
  if (value !== undefined && !object(value)) {
    if (action === 'untrust') return { value };
    throw new Stop('the autopilot value in pdd.json on GitHub is not an object; set a mode there first with pdd autopilot off, observe or auto');
  }
  const list = object(value) && Array.isArray(value.trust) ? value.trust : [];
  if (action === 'trust') {
    const added = unique(names).filter(name => !list.some(item => sameName(item, name)));
    return added.length ? { value: { ...(value ?? { mode: 'off' }), trust: [...list, ...added] }, message: `Add ${added.map(clean).join(', ')} to the PDD Autopilot trust list` } : { value };
  }
  const kept = list.filter(item => !sameName(item, names[0]));
  return kept.length < list.length ? { value: { ...value, trust: kept }, message: `Remove ${clean(names[0])} from the PDD Autopilot trust list` } : { value };
}

// A scanner for text that JSON.parse already accepted. It finds where each value is, so pdd changes only those bytes.
const space = (text, at) => { while (' \t\n\r'.includes(text[at] || '-')) at++; return at; };
const stringEnd = (text, at) => { for (at++; text[at] !== '"'; at++) if (text[at] === '\\') at++; return at + 1; };
function valueEnd(text, at) {
  if (text[at] === '"') return stringEnd(text, at);
  if (text[at] === '{' || text[at] === '[') {
    for (let depth = 0; ; at++) {
      if (text[at] === '"') at = stringEnd(text, at) - 1;
      else if (text[at] === '{' || text[at] === '[') depth++;
      else if ((text[at] === '}' || text[at] === ']') && --depth === 0) return at + 1;
    }
  }
  while (at < text.length && !',}] \t\n\r'.includes(text[at])) at++;
  return at;
}
function members(text, open) {
  const list = [];
  let at = space(text, open + 1);
  while (text[at] !== '}') {
    const keyEnd = stringEnd(text, at), start = space(text, space(text, keyEnd) + 1), end = valueEnd(text, start);
    list.push({ key: JSON.parse(text.slice(at, keyEnd)), keyStart: at, keyEnd, start, end });
    at = space(text, end);
    if (text[at] === ',') at = space(text, at + 1);
  }
  return { open, close: at, list };
}
const lineIndent = (text, at) => /^[ \t]*/.exec(text.slice(text.lastIndexOf('\n', at - 1) + 1))[0];
const top = text => members(text, space(text, 0));
// A value in the style of its place: on several lines with the indent unit of the file, or on one line.
function render(value, { multiline, unit, indent, spaced, eol }) {
  if (multiline) return JSON.stringify(value, null, unit).replace(/\n/g, `${eol}${indent}`);
  const comma = spaced ? ', ' : ',', colon = spaced ? ': ' : ':';
  const inline = item => Array.isArray(item) ? `[${item.map(inline).join(comma)}]`
    : object(item) ? `{${Object.entries(item).map(([key, entry]) => `${JSON.stringify(key)}${colon}${inline(entry)}`).join(comma)}}` : JSON.stringify(item);
  return inline(value);
}
// Sets key in the object box: in place of the old value text of member, else as a new last member.
function setMember(text, box, key, value, member) {
  const root = top(text), first = root.list[0];
  const pretty = !root.list.length || text.slice(root.open, root.close).includes('\n');
  const unit = (pretty && first && lineIndent(text, first.keyStart).slice(lineIndent(text, root.open).length)) || '  ';
  const eol = text.includes('\r\n') ? '\r\n' : '\n';
  if (member) {
    const old = text.slice(member.start, member.end), filled = /^[[{]\s*[^\s\]}]/.test(old);
    const multiline = old.includes('\n') || !filled && text.slice(box.open, box.close).includes('\n');
    const spaced = old.includes(',') ? /,\s/.test(old) : text.slice(member.keyEnd, member.start).includes(' ');
    return text.slice(0, member.start) + render(value, { multiline, unit, indent: lineIndent(text, member.start), spaced, eol }) + text.slice(member.end);
  }
  if (!box.list.length) {
    const outer = lineIndent(text, box.open), inner = outer + unit;
    const body = pretty ? `${eol}${inner}${JSON.stringify(key)}: ${render(value, { multiline: true, unit, indent: inner, eol })}${eol}${outer}`
      : `${JSON.stringify(key)}:${render(value, { multiline: false, spaced: false })}`;
    return text.slice(0, box.open + 1) + body + text.slice(box.close);
  }
  const [one, two] = box.list, last = box.list.at(-1);
  const gap = two ? text.slice(one.end, two.keyStart) : `,${text.slice(box.open + 1, one.keyStart)}`, colon = text.slice(one.keyEnd, one.start);
  const multiline = gap.includes('\n'), indent = multiline ? gap.slice(gap.lastIndexOf('\n') + 1) : lineIndent(text, last.keyStart);
  return text.slice(0, last.end) + gap + JSON.stringify(key) + colon + render(value, { multiline, unit, indent, spaced: colon.includes(' '), eol }) + text.slice(last.end);
}
function editAutopilot(text, before, after) {
  const root = top(text), holder = root.list.findLast(member => member.key === 'autopilot');
  if (!holder || !object(before) || !object(after)) return setMember(text, root, 'autopilot', after, holder);
  let result = text;
  for (const field of Object.keys(after)) {
    if (same(before[field], after[field])) continue;
    const inner = members(result, top(result).list.findLast(member => member.key === 'autopilot').start);
    result = setMember(result, inner, field, after[field], inner.list.findLast(member => member.key === field));
  }
  return result;
}
// The GitHub text with only the autopilot value changed: the indent, the key order and all other bytes stay.
function textFor(remote, value) {
  const expected = { ...remote.config, autopilot: value }, fallback = `${JSON.stringify(expected, null, 2)}\n`;
  if (remote.text === undefined) return fallback;
  try {
    const text = editAutopilot(remote.text, remote.config.autopilot, value);
    if (same(parse(text), expected)) return text;
  } catch { /* The plain JSON text below is still correct. */ }
  return fallback;
}
const writeFile = (github, repository, branch, remote, value, message) => ask(github, { method: 'PUT', path: `repos/${repository}/contents/pdd.json`,
  body: { message, content: Buffer.from(textFor(remote, value)).toString('base64'), branch, ...(remote.sha ? { sha: remote.sha } : {}) } });
// After a refusal: a new blob sha means that another change came between the read and the write (a race), the same sha means that the branch refuses.
const raced = async (github, repository, branch, remote) => (await readRemote(github, repository, branch)).sha !== remote.sha;
const titleFor = (value, base) => modeOf(value) !== 'off' && modeOf(base) === 'off' ? 'Turn on PDD Autopilot' : 'Update PDD Autopilot settings';
const bodyFor = (value, branch) => `This PR changes only \`autopilot\` in \`pdd.json\`. The new value:\n\n\`\`\`json\n${JSON.stringify(value, null, 2)}\n\`\`\`\n\n`
  + `${clean(branch)} does not accept a direct change. Autopilot workers start from ${clean(branch)}, so they use this setting only after the merge. While this PR is open, the next pdd autopilot command updates it.\n`;
async function closePull(github, repository, pull, note) {
  await ask(github, { method: 'POST', path: `repos/${repository}/issues/${pull.number}/comments`, body: { body: note } });
  const answer = await ask(github, { method: 'PATCH', path: `repos/${repository}/pulls/${pull.number}`, body: { state: 'closed' } });
  if (!success(answer?.status)) throw new Stop(`GitHub did not close ${clean(pull.html_url)} (HTTP ${answer?.status})`);
}

async function publishOnce({ github, repository, defaultBranch, change, ports }) {
  const base = clean(defaultBranch), what = change.action === 'mode' ? 'the new mode' : 'the new trust list';
  const main = await readRemote(github, repository, defaultBranch);
  const [pull, ...older] = await settingsPulls(github, repository, defaultBranch);
  if (pull) {
    // The open PR collects the pending changes, so this command builds on its value.
    const branch = pull.head.ref, url = clean(pull.html_url);
    const remote = await readRemote(github, repository, branch);
    const { value, message } = apply(change, remote.config.autopilot);
    if (same(value, main.config.autopilot)) {
      for (const each of [pull, ...older]) await closePull(github, repository, each, `pdd closed this PR: ${base} already has these Autopilot settings.`);
      return { state: 'closed', lines: [`pdd closed ${[pull, ...older].map(each => clean(each.html_url)).join(', ')}, because ${base} already has this setting.`], value, place: 'GitHub' };
    }
    for (const each of older) await closePull(github, repository, each, `pdd closed this PR: ${url} has the newest Autopilot settings.`);
    if (!message) return { state: 'pull-request', lines: [`The open PR ${url} already has this setting. Merge it before Autopilot workers use ${what}.`], value, place: 'the PR' };
    const written = await writeFile(github, repository, branch, remote, value, message);
    if (!success(written?.status)) {
      if (REFUSED.includes(written?.status) && await raced(github, repository, branch, remote)) return RACE;
      throw new Stop(`GitHub refused the change on ${clean(branch)} (HTTP ${written?.status})`);
    }
    try { await ask(github, { method: 'PATCH', path: `repos/${repository}/pulls/${pull.number}`, body: { title: titleFor(value, main.config.autopilot), body: bodyFor(value, defaultBranch) } }); }
    catch { /* The commit is on the PR; an old title does not change the result. */ }
    return { state: 'pull-request', lines: [`pdd updated the open PR ${url}. Merge it before Autopilot workers use ${what}.`], value, place: 'the PR' };
  }
  const { value, message } = apply(change, main.config.autopilot);
  if (!message) return { state: 'current', lines: ['pdd.json on GitHub is already up to date.'], value, place: 'GitHub' };
  const direct = await writeFile(github, repository, defaultBranch, main, value, message);
  if (success(direct?.status)) {
    const commit = direct.body?.commit;
    const url = typeof commit?.html_url === 'string' ? commit.html_url : typeof commit?.sha === 'string' ? `https://github.com/${repository}/commit/${commit.sha}` : '';
    return { state: 'written', lines: [`Updated pdd.json on GitHub (${base})${url ? `: ${clean(url)}` : '.'}`], value, place: 'GitHub', pull: true };
  }
  if (!REFUSED.includes(direct?.status)) throw new Stop(`GitHub refused the change (HTTP ${direct?.status})`);
  if (await raced(github, repository, defaultBranch, main)) return RACE;
  // The same blob sha: the default branch itself wants a PR. The same one-file change goes on a new branch.
  const head = await ask(github, { method: 'GET', path: `repos/${repository}/git/ref/heads/${segments(defaultBranch)}` });
  if (!success(head?.status) || typeof head.body?.object?.sha !== 'string') throw new Stop(`GitHub did not send the head of ${base} (HTTP ${head?.status})`);
  const branch = `${PREFIX}${(ports.shortId ?? (() => randomBytes(4).toString('hex')))()}`;
  const created = await ask(github, { method: 'POST', path: `repos/${repository}/git/refs`, body: { ref: `refs/heads/${branch}`, sha: head.body.object.sha } });
  if (!success(created?.status)) throw new Stop(created?.status === 403 ? `you cannot push to ${clean(repository)} (HTTP 403)`
    : `${base} does not accept a direct change, and GitHub refused the branch ${branch} (HTTP ${created?.status})`);
  const onBranch = await readRemote(github, repository, branch);
  const next = apply(change, onBranch.config.autopilot);
  if (!next.message) return { state: 'current', lines: ['pdd.json on GitHub is already up to date.'], value: next.value, place: 'GitHub' };
  const written = await writeFile(github, repository, branch, onBranch, next.value, next.message);
  if (!success(written?.status)) throw new Stop(`${base} does not accept a direct change, and GitHub refused the change on ${branch} (HTTP ${written?.status})`);
  const opened = await ask(github, { method: 'POST', path: `repos/${repository}/pulls`, body: { title: titleFor(next.value, main.config.autopilot), head: branch, base: defaultBranch, body: bodyFor(next.value, defaultBranch) } });
  if (!success(opened?.status) || typeof opened.body?.html_url !== 'string') throw new Stop(`branch ${branch} has the change, but GitHub did not open the PR (HTTP ${opened?.status}); open a PR from it to ${base}`);
  return { state: 'pull-request', lines: [`${base} does not accept a direct change, so pdd opened ${clean(opened.body.html_url)}. Merge it before Autopilot workers use ${what}.`], value: next.value, place: 'the PR' };
}

export async function publishAutopilotSettings({ cwd, action, mode, names, retry } = {}, ports = {}) {
  const again = clean(retry || 'the same pdd autopilot command');
  const notUpdated = reason => ({ state: 'not-updated', message: `pdd.json on GitHub was not updated: ${reason}. This checkout has the new setting. To retry, run ${again}.` });
  const change = { action, mode, names };
  if (!valid(change)) return { state: 'skipped', message: '' };
  try {
    let found;
    try { found = await context(cwd, ports); } catch { return notUpdated('the local pdd.json could not be read'); }
    const { local, github } = found;
    if (!object(local)) return { state: 'skipped', message: '' };
    const { repository, defaultBranch } = await repositoryOf(github);
    // One more round after a race: read again and apply the change to the new GitHub value.
    for (let round = 0; round < 2; round++) {
      const outcome = await publishOnce({ github, repository, defaultBranch, change, ports });
      if (outcome === RACE) continue;
      const lines = [...outcome.lines];
      if (!sameSettings(outcome.value, local)) lines.push(`This checkout has other Autopilot settings (${outcome.place}: ${settings(outcome.value)}; this checkout: ${settings(local)}).`);
      if (outcome.pull) lines.push('pdd.json on GitHub is updated. To update your local copy, run git restore pdd.json, then git pull.');
      return { state: outcome.state, message: lines.join('\n') };
    }
    return notUpdated(`pdd.json on ${clean(defaultBranch)} changed again while pdd wrote it`);
  } catch (error) {
    return notUpdated(error instanceof Stop ? error.message : 'an unexpected error stopped the update');
  }
}

// The commands that make the GitHub copy equal to this checkout.
function commands(remote, local) {
  const theirs = namesOf(remote), ours = namesOf(local);
  const add = unique(ours.filter(name => !theirs.some(item => sameName(item, name))));
  const remove = unique(theirs.filter(name => !ours.some(item => sameName(item, name))));
  return [...(modeOf(remote) === modeOf(local) ? [] : [`pdd autopilot ${modeOf(local)}`]),
    ...(add.length ? [`pdd autopilot trust ${add.map(clean).join(' ')}`] : []), ...remove.map(name => `pdd autopilot untrust ${clean(name)}`)];
}

export async function checkAutopilotSettings({ cwd } = {}, ports = {}) {
  try {
    const { local, github } = await context(cwd, ports);
    const { repository, defaultBranch } = await repositoryOf(github);
    const remote = (await readRemote(github, repository, defaultBranch)).config.autopilot;
    let pull;
    try { [pull] = await settingsPulls(github, repository, defaultBranch); } catch { pull = undefined; }
    const differ = !sameSettings(remote, local);
    if (!differ && !pull) return { state: 'same', message: '' };
    const parts = [];
    if (differ) parts.push(`pdd.json on GitHub (${clean(defaultBranch)}) has other Autopilot settings (GitHub: ${settings(remote)}; this checkout: ${settings(local)}). Autopilot workers use the GitHub copy.`);
    if (pull) parts.push(`The settings PR ${clean(pull.html_url)} is open: Autopilot workers use its change only after the merge.`);
    if (differ) parts.push(`To change the GitHub copy, run ${commands(remote, local).join(' and ')}.`);
    return { state: 'different', message: `Warning: ${parts.join(' ')}` };
  } catch { return { state: 'unknown', message: '' }; }
}
