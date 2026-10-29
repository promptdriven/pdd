// Generated from prompts/cli/try-mailbox.prompt.md (sha256: 3af752e229504c75714fc34475824e595c416c734a508c5e2c7d6ed602732c9c).
import { randomUUID } from 'node:crypto';
import { closeSync, constants, existsSync, lstatSync, mkdirSync, openSync, readFileSync, readdirSync, realpathSync, renameSync, unlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, relative, sep } from 'node:path';
import { cleanText } from './runtime-output.mjs';
import { runDoorCall } from './runtime-client.mjs';
const uuid = /^[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}$/i;
const stop = message => { throw new Error(message); };
function regular(root, path) {
  folder(root, dirname(path));
  const stat = lstatSync(path);
  if (!stat.isFile() || stat.isSymbolicLink() || stat.nlink !== 1 || (stat.mode & 0o077)) stop(`Unsafe private Try file: ${path}`);
  return stat;
}
function folder(root, path) {
  const rel = relative(root, path);
  if (!rel || rel.startsWith('..') || rel.startsWith(sep) || realpathSync(root) !== root) stop('The mailbox must stay inside the workspace.');
  let current = root;
  for (const part of rel.split(sep)) {
    current = join(current, part);
    try { mkdirSync(current, { mode: 0o700 }); } catch (e) { if (e.code !== 'EEXIST') throw e; }
    const stat = lstatSync(current);
    if (!stat.isDirectory() || stat.isSymbolicLink() || (stat.mode & 0o077)) stop(`Unsafe private Try folder: ${current}`);
  }
  return path;
}
function load(root, path) { regular(root, path); return JSON.parse(readFileSync(path, 'utf8')); }
function publish(root, path, value) {
  folder(root, dirname(path));
  try { regular(root, path); } catch (e) { if (e.code !== 'ENOENT') throw e; }
  const temp = `${path}.${randomUUID()}.tmp`;
  const fd = openSync(temp, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | constants.O_NOFOLLOW, 0o600);
  try { writeFileSync(fd, JSON.stringify(value)); } finally { closeSync(fd); }
  try { renameSync(temp, path); } finally { try { unlinkSync(temp); } catch {} }
}
function claim(root, path, value = { pid: process.pid }) {
  folder(root, dirname(path));
  const fd = openSync(path, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | constants.O_NOFOLLOW, 0o600);
  try { writeFileSync(fd, JSON.stringify(value)); } finally { closeSync(fd); }
}
const pause = (ms, signal) => new Promise(done => {
  const timer = setTimeout(finish, ms);
  function finish() { clearTimeout(timer); signal?.removeEventListener('abort', finish); done(); }
  signal?.addEventListener('abort', finish, { once: true });
  if (signal?.aborted) finish();
});
export function prepareMailbox(root, sessionId) {
  if (!/^[A-Za-z0-9-]+$/.test(sessionId ?? '')) stop('Invalid Try session ID.');
  const base = folder(root, join(root, '.pdd/try/mailbox', sessionId));
  for (const child of ['requests', 'replies', 'claims']) folder(root, join(base, child));
  return base;
}
function location(d) {
  const base = prepareMailbox(d.root, d.sessionId);
  if (d.mailbox !== base) stop('The mailbox record does not match this workspace and Try.');
  return base;
}
export async function mailboxCall(d, input, ports = {}) {
  const base = location(d), heartbeat = join(base, 'owner.json');
  let owner;
  try { owner = load(d.root, heartbeat); } catch (e) { if (e.code !== 'ENOENT') throw e; }
  if (!owner || owner.sessionId !== d.sessionId || !Number.isFinite(owner.time) || Math.abs(Date.now() - owner.time) > 5000)
    stop('No owner mailbox is running. Keep pdd try STORY --cli open in a terminal outside the agent sandbox.');
  if (['login','origin','promptHash'].some(key => owner[key] !== d[key])) stop('This Try mailbox belongs to another owner or source. Run pdd try STORY --cli again.');
  if (ports.signal?.aborted) stop('The command was not sent.');
  const id = randomUUID(), end = Date.now() + 900_000;
  let told = false;
  publish(d.root, join(base, 'requests', `${id}.json`), { id, sessionId: d.sessionId, input });
  const answerPath = join(base, 'replies', `${id}.json`);
  for (;;) {
    if (ports.signal?.aborted) stop(`The command result is unknown (${id}). Do not repeat it automatically.`);
    folder(d.root, dirname(answerPath));
    const progressPath = join(base, 'replies', `${id}.progress.json`);
    if (!told && existsSync(progressPath)) { const progress = load(d.root, progressPath); if (progress.id === id && progress.sessionId === d.sessionId) { ports.stderr?.write('pdd try: waiting for the current Try action…\n'); told = true; } }
    if (existsSync(answerPath)) {
      const answer = load(d.root, answerPath);
      if (answer.id !== id || answer.sessionId !== d.sessionId) stop('The mailbox returned a different command. Do not repeat it automatically.');
      if (answer.error) throw Object.assign(new Error(answer.error), { tryUsage: answer.usage });
      if (!answer.answer || typeof answer.answer !== 'object') stop('The mailbox result is invalid. Do not repeat it automatically.');
      return answer.answer;
    }
    let alive;
    try { alive = load(d.root, heartbeat); } catch (e) { if (e.code !== 'ENOENT') throw e; }
    if (Date.now() >= end || !alive || alive.generation !== owner.generation || Math.abs(Date.now() - alive.time) > 5000)
      stop(`The command result is unknown (${id}); the owner mailbox stopped or timed out. Do not repeat it automatically.`);
    await pause(50, ports.signal);
  }
}
function validRequest(r, id, d) {
  return r?.id === id && r.sessionId === d.sessionId && Object.keys(r).every(k => ['id', 'sessionId', 'input'].includes(k))
    && r.input && Object.keys(r.input).every(k => ['argv', 'stdin'].includes(k))
    && Array.isArray(r.input.argv) && r.input.argv.every(v => typeof v === 'string')
    && (r.input.stdin === undefined || (typeof r.input.stdin === 'string' && Buffer.byteLength(r.input.stdin) <= 1024 * 1024));
}
export function watchMailbox(context, d) {
  const base = location(d), lock = join(base, 'relay.lock'), heartbeat = join(base, 'owner.json');
  const generation = randomUUID();
  try { claim(d.root, lock, {pid:process.pid,generation}); } catch (e) {
    if (e.code !== 'EEXIST') throw e;
    regular(d.root, lock); stop(`A mailbox owner already holds ${lock}. Check its process before removing an abandoned lock.`);
  }
  const lockInode = lstatSync(lock).ino;
  const owner = () => ({ sessionId: d.sessionId, login: d.login, origin: d.origin, promptHash: d.promptHash, generation, pid: process.pid, time: Date.now() });
  try { publish(d.root, heartbeat, owner()); } catch (e) { unlinkSync(lock); throw e; }
  let heartbeatError;
  const timer = setInterval(() => { try { publish(d.root, heartbeat, owner()); } catch (e) { heartbeatError = e; } }, 1000);
  return (async () => {
    try {
      while (!context.signal?.aborted) {
        if (heartbeatError) throw heartbeatError;
        folder(d.root, join(base, 'requests'));
        for (const filename of readdirSync(join(base, 'requests')).sort()) {
          if (context.signal?.aborted) break;
          const id = filename.slice(0, -5);
          if (!filename.endsWith('.json') || !uuid.test(id)) continue;
          const requestPath = join(base, 'requests', filename), answerPath = join(base, 'replies', filename);
          folder(d.root, dirname(answerPath));
          if (existsSync(answerPath)) { regular(d.root, answerPath); continue; }
          const claimed = join(base, 'claims', id);
          let response;
          try {
            const stat = regular(d.root, requestPath);
            if (stat.size > 2 * 1024 * 1024) stop('The mailbox request exceeds 2 MiB.');
            const request = load(d.root, requestPath);
            if (!validRequest(request, id, d)) stop('The mailbox request is invalid.');
            try { claim(d.root, claimed); } catch (e) {
              if (e.code !== 'EEXIST') throw e;
              regular(d.root, claimed); stop('The command result is unknown after a previous dispatch. Do not repeat it automatically.');
            }
            const answer = await runDoorCall(d, request.input, { ...context.ports, signal: context.signal,
              onDoorProgress: () => publish(d.root, join(base, 'replies', `${id}.progress.json`), {id,sessionId:d.sessionId}),
              doorState: { identity: context.identity, store: context.store } });
            response = { answer };
          } catch (e) { response = { error: cleanText(e.message || 'The command result is unknown. Do not repeat it automatically.', [context.identity.token]), usage: e.tryUsage }; }
          if (context.signal?.aborted) break;
          // Even a malicious server echo cannot write the owner credential into the workspace.
          const safe = JSON.parse(JSON.stringify({ id, sessionId: d.sessionId, ...response }).split(context.identity.token).join('[secret]'));
          publish(d.root, answerPath, safe);
        }
        await pause(50, context.signal);
      }
      return 0;
    } finally {
      clearInterval(timer);
      try { if (load(d.root, heartbeat).generation === generation) { regular(d.root, heartbeat); unlinkSync(heartbeat); } } catch (e) { if (e.code !== 'ENOENT') throw e; }
      try { if (regular(d.root, lock).ino === lockInode && load(d.root, lock).generation === generation) unlinkSync(lock); } catch (e) { if (e.code !== 'ENOENT') throw e; }
    }
  })();
}
