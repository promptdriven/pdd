import { appendFileSync, existsSync, readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { delimiter, dirname, join } from 'node:path';
import { fakeHerdr } from '../helpers/fake-herdr.mjs';
import { createGithubRepoFake } from '../helpers/github-repo-fake.mjs';

const [control, tool, ...args] = process.argv.slice(2);
const world = JSON.parse(readFileSync(join(control, 'world.json'), 'utf8'));
const readStdin = () => { try { return readFileSync(0, 'utf8'); } catch { return ''; } };
const wantsStdin = tool === 'gh' && args.includes('--input') && args[args.indexOf('--input') + 1] === '-';
const input = wantsStdin ? readStdin() : '';
const digest = text => createHash('sha256').update(text).digest('hex').slice(0, 16);

const reply = { http: '' };
process.on('exit', code => {
  const meta = [input ? `stdin=${digest(input)}` : '', `exit=${process.exitCode ?? code}`, reply.http ? `http=${reply.http}` : ''].filter(Boolean).join(';');
  appendFileSync(join(control, 'calls.log'), [tool, process.cwd(), meta, ...args].join('\x1f') + '\x1e');
});

const out = text => process.stdout.write(text);
const fail = (code, text) => { process.stderr.write(text); process.exitCode = code; };

function githubWorld() {
  const spec = world.github ?? {};
  const fake = createGithubRepoFake({ repository: spec.repository ?? 'acme/widgets', owner: spec.owner ?? 'acme', issues: spec.issues ?? 20,
    now: () => Date.parse(spec.now ?? '2026-11-13T12:00:00Z') });
  for (const [verb, ...rest] of spec.changes ?? []) fake[verb](...rest);
  return fake;
}

const writeMethods = new Set(['POST', 'PATCH', 'PUT', 'DELETE']);
const valueFlags = new Set(['--method', '-X', '-H', '--header', '--input', '-f', '-F', '--raw-field', '--field', '--jq', '-q', '--template', '-t', '--hostname', '--cache']);
const fieldFlags = new Set(['-f', '-F', '--raw-field', '--field']);
const flagValue = (list, ...names) => { const index = list.findIndex(word => names.includes(word)); return index < 0 ? undefined : list[index + 1]; };
const endpointOf = list => list.find((word, index) => index > 0 && !word.startsWith('-') && !valueFlags.has(list[index - 1]));
const methodOf = list => (flagValue(list, '--method', '-X') ?? (list.includes('--input') || list.some(word => fieldFlags.has(word)) ? 'POST' : 'GET')).toUpperCase();
const fieldBody = list => {
  const body = {};
  list.forEach((word, index) => {
    if (!fieldFlags.has(word)) return;
    const [key, ...rest] = String(list[index + 1]).split('='), value = rest.join('=');
    if (key.endsWith('[]')) body[key.slice(0, -2)] = [...(body[key.slice(0, -2)] ?? []), value];
    else body[key] = value;
  });
  return JSON.stringify(body);
};
const httpReply = (status, body) => ({ code: status < 300 ? 0 : 1, stdout: [`HTTP/2.0 ${status} ${status < 300 ? 'OK' : 'Error'}`, 'X-Ratelimit-Limit: 5000', 'X-Ratelimit-Remaining: 4999', 'X-Ratelimit-Resource: core', '', JSON.stringify(body)].join('\r\n'), stderr: status < 300 ? '' : `gh: HTTP ${status}\n` });

async function githubRoute(fake, request, body) {
  const method = methodOf(request), endpoint = endpointOf(request) ?? '', prefix = `repos/${fake.repo}/`;
  const route = endpoint.toLowerCase().startsWith(prefix) ? endpoint.slice(prefix.length) : null;
  if (method === 'POST' && route === 'labels') {
    const { name } = JSON.parse(body ?? '{}');
    if (fake.repoLabels.has(name)) return httpReply(422, { message: 'Validation Failed', errors: [{ resource: 'Label', code: 'already_exists', field: 'name' }] });
    fake.repoLabels.add(name); return httpReply(201, { name });
  }
  const labelled = /^issues\/([0-9]+)\/labels$/.exec(route ?? '');
  if (method === 'POST' && labelled && fake.issues.has(Number(labelled[1]))) {
    for (const name of JSON.parse(body ?? '{}').labels ?? []) if (!fake.issues.get(Number(labelled[1])).labels.includes(name)) fake.label(Number(labelled[1]), name);
    return httpReply(200, fake.issues.get(Number(labelled[1])).labels.map(name => ({ name })));
  }
  return fake.gh(request, { input: body });
}

async function github() {
  const fake = githubWorld(), log = join(control, 'gh-writes.jsonl');
  fake.repoLabels = new Set();
  const previous = existsSync(log) ? readFileSync(log, 'utf8').split('\n').filter(Boolean).map(line => JSON.parse(line)) : [];
  for (const write of previous) await githubRoute(fake, write.args, write.input);
  if (args[0] === 'auth') return;
  if (args[0] === 'repo') return out(JSON.stringify({ nameWithOwner: fake.repo, url: `https://github.com/${fake.repo}`, defaultBranchRef: { name: 'main' }, owner: { login: fake.owner } }));
  if (args[0] === 'pr' && args[1] === 'list') return out('[]');
  if (args[0] !== 'api') return fail(1, `golden gh: unsupported gh ${args.slice(0, 2).join(' ')}\n`);
  const method = methodOf(args), body = args.some(word => fieldFlags.has(word)) ? fieldBody(args) : input || undefined;
  const plain = args.filter((word, index) => !fieldFlags.has(word) && !fieldFlags.has(args[index - 1]));
  const request = plain.includes('--method') || plain.includes('-X') ? plain : [plain[0], '--method', method, ...plain.slice(1)];
  const answer = await githubRoute(fake, request, body);
  reply.http = /^HTTP\/\S+ (\d+)/.exec(answer.stdout)?.[1] ?? '';
  if (writeMethods.has(method) && answer.code === 0) appendFileSync(log, JSON.stringify({ args: request, input: body }) + '\n');
  const include = args.includes('--include') || args.includes('-i');
  const text = include ? answer.stdout : answer.stdout.slice(answer.stdout.indexOf('\r\n\r\n') + 4);
  out(text); if (answer.stderr) process.stderr.write(answer.stderr); process.exitCode = answer.code;
}

async function herdr() {
  const shimFolder = join(dirname(control), 'bin');
  process.env.PATH = process.env.PATH.split(delimiter).filter(folder => folder !== shimFolder).join(delimiter);
  const words = args[0] === '--session' ? args.slice(2) : args;
  if (words[0] === '--version' || words[0] === 'version') return out('herdr 0.9.1\n');
  const file = join(control, 'herdr.json'), fake = fakeHerdr();
  if (existsSync(file)) Object.assign(fake, JSON.parse(readFileSync(file, 'utf8')));
  else Object.assign(fake, world.herdr ?? {});
  fake.now = () => Date.parse('2026-11-13T12:00:00Z');
  try {
    const reply = await fake.herdr(words);
    out(typeof reply === 'string' ? reply : JSON.stringify(reply));
  } catch (error) {
    out(JSON.stringify({ error: { code: error.code ?? error.message, message: error.message } })); process.exitCode = 1;
  } finally {
    const { now, ...saved } = fake;
    writeFileSync(file, JSON.stringify(saved));
  }
}

function agent() {
  if (tool === 'codex' && args[0] === 'login') return out('Logged in using ChatGPT\n');
  if (tool === 'claude' && args[0] === 'auth') return out(JSON.stringify({ loggedIn: true }));
  if (args[0] === '--version') return out(`${tool} 1.0.0\n`);
  return fail(1, `golden ${tool}: no model calls\n`);
}

function timer() {
  if (tool === 'launchctl') return fail(113, 'Could not find service in domain.\n');
  if (tool === 'systemctl') { out('inactive\n'); process.exitCode = 3; return; }
  if (tool === 'loginctl') return out('no\n');
}

if (tool === 'gh') await github();
else if (tool === 'herdr') await herdr();
else if (tool === 'codex' || tool === 'claude') agent();
else timer();
