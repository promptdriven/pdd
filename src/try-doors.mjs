// Generated from prompts/cli/try-doors.prompt.md (sha256: c0bea5217562064448b973ae4d7e70b8582a1260898b0e003c37c03288c6750c).
import { spawn } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { chmodSync, closeSync, constants, existsSync, lstatSync, mkdirSync, openSync, readFileSync, realpathSync, renameSync, unlinkSync, writeFileSync } from 'node:fs';
import { basename, dirname, join, relative, resolve, sep } from 'node:path';
import { readPrompt } from './runtime-preflight.mjs';
import { cleanText, tryUsage, tryUsageLine } from './runtime-output.mjs';
import { runDoorCall, saveDoorCase } from './runtime-client.mjs';
import { prepareMailbox, mailboxCall, watchMailbox } from './try-mailbox.mjs';
import { installNamedLauncher } from './try-launcher.mjs';

const WRAPPER_EXIT = 125;
const hash = text => createHash('sha256').update(text).digest('hex');
const quote = word => /^[A-Za-z0-9_./:@%+=,-]+$/.test(word) ? word : `'${word.replaceAll("'", "'\\''")}'`;
const read = path => JSON.parse(readFileSync(path, 'utf8'));
const fail = message => { const e = new Error(message); e.exitCode = WRAPPER_EXIT; throw e; };
function regular(path) {
  const stat = lstatSync(path);
  if (stat.isSymbolicLink()) fail('Refusing a symbolic link in Try files.');
  if (!stat.isFile() || stat.nlink !== 1) fail('A Try file must be a regular file with one link.');
}
function workspaceFile(root, path) {
  const rel = relative(root, path);
  if (!rel || rel.startsWith('..') || rel.startsWith(sep) || realpathSync(root) !== root) fail('The Try file must stay inside the workspace.');
  let current = root;
  for (const part of rel.split(sep)) {
    current = join(current, part);
    const stat = lstatSync(current);
    if (stat.isSymbolicLink()) fail('Refusing a symbolic link in workspace Try files.');
  }
}
function writePrivate(path, value) {
  if (existsSync(path)) regular(path);
  const temp = `${path}.${process.pid}.tmp`;
  const fd = openSync(temp, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | constants.O_NOFOLLOW, 0o600);
  try { writeFileSync(fd, JSON.stringify(value, null, 2) + '\n'); } finally { closeSync(fd); }
  renameSync(temp, path);
}
function privateDir(root, target) {
  let path = root;
  const rel = relative(root, target);
  if (!rel || rel.startsWith('..') || rel.startsWith(sep)) fail('The Try state must stay inside the workspace.');
  for (const part of rel.split(sep)) {
    path = join(path, part);
    try { mkdirSync(path, { mode: 0o700 }); } catch (e) { if (e.code !== 'EEXIST') throw e; }
    const stat = lstatSync(path);
    if (stat.isSymbolicLink()) fail(`Refusing a symbolic link at ${part}.`);
    if (!stat.isDirectory()) fail(`${part} is not a folder.`);
    chmodSync(path, 0o700);
  }
  return path;
}

function cliEntry(context, test) {
  const entries = new Map();
  for (const step of test.doc.steps) {
    const prompt = readPrompt(context.root, context.visible, step.entry_path);
    const index = prompt.interface?.entries?.findIndex(e => e.operation === step.operation);
    if (!(index >= 0)) continue;
    const conventions = prompt.interface.conventions ?? [];
    if (!['input_schema', 'result_schema'].every(key => conventions.some(c => c.path === `/entries/${index}/${key}` && c.convention === 'cli'))) continue;
    entries.set(`${step.entry_path}#${step.operation}`, { step, prompt, entry: prompt.interface.entries[index] });
  }
  if (entries.size !== 1) fail(entries.size ? 'This Story uses several CLI entries; choose a Story with one CLI entry.' : 'This Story has no CLI entry. Mark both schemas with the cli convention (RUNBOOK §6).');
  const value = [...entries.values()][0];
  const heading = value.prompt.text.match(/^#\s+(.+?)\s*$/m)?.[1]?.replace(/^`([^`]+)`$/, '$1');
  if (!/^[A-Za-z][A-Za-z0-9._-]{0,63}$/.test(heading ?? '') || ['pdd', 'node', 'gh', 'git'].includes(heading?.toLowerCase())) fail('Name the program in the CLI prompt’s first heading, for example # tipjar; pdd, node, gh and git are reserved (RUNBOOK §6).');
  return { ...value, name: heading };
}

export async function openCli(context, test, sessionId, options) {
  const { root, ports, store, identity, origin } = context;
  const { step, prompt, entry, name } = cliEntry(context, test);
  const record = store.repo(root).tries?.[test.path];
  if (record?.prompt_hashes?.[step.entry_path] !== hash(prompt.text)) fail('The CLI prompt changed or this Try has no source record. Run pdd try STORY --cli --new.');
  for (const [path, expected] of Object.entries(record.prompt_hashes)) if (hash(readFileSync(join(root, path))) !== expected) fail('A prompt dependency changed since this Try. Run pdd try STORY --cli --new.');
  privateDir(root, join(root, '.pdd/try'));
  // A local exclude is preferable to changing the project's tracked .gitignore.
  const { spawnSync } = await import('node:child_process');
  const git = spawnSync('git', ['rev-parse', '--git-path', 'info/exclude'], { cwd: root, encoding: 'utf8' });
  if (git.status !== 0) fail('Could not locate the repository’s local Git exclude file.');
  const exclude = git.stdout.trim().startsWith('/') ? git.stdout.trim() : join(root, git.stdout.trim());
  if (existsSync(exclude)) regular(exclude);
  mkdirSync(dirname(exclude), { recursive: true });
  if (realpathSync(dirname(exclude)) !== dirname(exclude)) fail('Refusing a symbolic link in the Git exclude path.');
  const ignored = existsSync(exclude) ? readFileSync(exclude, 'utf8') : '';
  if (!ignored.split('\n').includes('/.pdd/try/')) writeFileSync(exclude, `${ignored}${ignored.endsWith('\n') || !ignored ? '' : '\n'}/.pdd/try/\n`);
  const tracked = spawnSync('git', ['ls-files', '-z', '--', '.pdd/try'], { cwd: root, encoding: 'utf8' });
  if (tracked.status !== 0 || tracked.stdout) fail('Refusing to create a Try mailbox: .pdd/try contains tracked files. Untrack them first.');
  if (!/^[A-Za-z0-9-]+$/.test(sessionId)) fail('The Try session ID is invalid.');
  const stateDir = privateDir(root, join(root, '.pdd/try/sessions', sessionId));
  const mailbox = prepareMailbox(root, sessionId);
  if (spawnSync('git', ['check-ignore', '--quiet', '--no-index', '--', join(mailbox, 'owner.json')], { cwd: root }).status !== 0)
    fail('The Try mailbox is not Git-ignored. Ignore /.pdd/try/ before opening the CLI.');
  const descriptorPath = join(stateDir, 'door.json');
  if (existsSync(descriptorPath) && read(descriptorPath).promptHash !== hash(prompt.text)) fail('The CLI prompt changed since this Try. Run pdd try STORY --cli --new.');
  let metadata;
  try { const reply = await context.runtime.send(`/v1/try/${sessionId}/model`, { method: 'GET' }, 30_000); if (reply.status === 200) metadata = reply.json; } catch { /* Accounting cannot block an otherwise usable CLI. */ }
  const usage = tryUsage(metadata);
  ports.stderr.write(`${tryUsageLine(usage)}\n`);
  const descriptor = { callCap: usage.cap, version: 2, root, sessionId, origin, login: identity.login, prompt: step.entry_path, operation: step.operation,
    mailbox, runtimeStateDir: store.dir, promptHashes: record.prompt_hashes, name, inputSchema: entry.input_schema, originalPath: test.path, storyPath: test.doc.story_path, criteria: test.doc.criteria,
    criterion: step.checks[0]?.criterion_id, storyHash: hash(readFileSync(join(root, test.doc.story_path))),
    promptHash: hash(prompt.text), stateDir, repoState: join(store.folder('repos'), `${store.repoKey(root)}.json`) };
  writePrivate(descriptorPath, descriptor);
  const last = join(stateDir, 'last.json');
  if (!existsSync(last)) writePrivate(last, { state: 'unknown' });
  store.saveRepo(root, { ...store.repo(root), last_door: { descriptor: descriptorPath, last } });
  const executable = process.argv[1];
  const binDir = ports.cliBin ?? (executable && ['pdd','pdd.mjs'].includes(basename(executable)) ? dirname(resolve(executable)) : null);
  if (!binDir) fail('Cannot locate the installed pdd bin folder. Run the installed pdd command.');
  const installed = installNamedLauncher({root,name,descriptorPath,binDir,path:ports.env.PATH ?? process.env.PATH ?? ''});
  ports.stdout.write(`Try is ready: ${name}\n${installed}\nRun ${name} from this repository or a folder inside it.\n`);
  const examples = [...new Set(test.doc.steps.filter(s => s.entry_path === step.entry_path && s.operation === step.operation && Array.isArray(s.input?.argv))
    .map(s => [name, ...s.input.argv].map(quote).join(' ')))];
  if (examples.length) ports.stdout.write(`Examples from this Story:\n${examples.map(s => `  ${s}`).join('\n')}\n`);
  if (ports.cliRelay) return ports.cliRelay(context, descriptor);
  const relayController = new AbortController();
  const signal = context.signal ? AbortSignal.any([context.signal, relayController.signal]) : relayController.signal;
  const watching = watchMailbox({ ...context, signal }, descriptor);
  ports.stderr.write('pdd try: mailbox ready; keep this terminal open for agent commands. Ctrl-C stops the mailbox, not the Try.\n');
  if (options['--shell']) {
    const chosen = ports.env.SHELL || '/bin/sh', shell = ['bash', 'zsh', 'sh'].includes(basename(chosen)) ? chosen : '/bin/sh';
    const env = { ...ports.env, PATH: ports.env.PATH ?? process.env.PATH ?? '' };
    try {
      if (ports.shell) return await ports.shell(shell, env);
      return await new Promise((done, reject) => { const child = spawn(shell, ['-i'], { cwd: root, env, stdio: 'inherit' }); child.on('error', reject); child.on('exit', (code, signal) => done(code ?? (signal ? 128 : 0))); });
    } finally { relayController.abort(); await watching; }
  }
  return watching;
}

// Only workspace files are touched after setup. Normal Check/Try state stays outside the repo.
function workspaceState(d, descriptorPath) {
  const expected = join(d.root, '.pdd/try/sessions', d.sessionId);
  if (d.stateDir !== expected || resolve(descriptorPath) !== join(expected, 'door.json')) fail('The Try state must stay inside the workspace. Run pdd try STORY --cli again.');
  privateDir(d.root, expected);
}
async function waitTurn(d, ports) {
  const path = join(d.stateDir, 'command.lock'), end = Date.now() + (ports.queueMs ?? 60_000);
  let told = false;
  for (;;) {
    if (ports.signal?.aborted) fail('Stopped waiting for the Try; this command was not sent.');
    privateDir(d.root, d.stateDir);
    try {
      const fd = openSync(path, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | constants.O_NOFOLLOW, 0o600);
      const lease = randomUUID();
      try { writeFileSync(fd, JSON.stringify({ pid: process.pid, lease })); } finally { closeSync(fd); }
      return () => { privateDir(d.root, d.stateDir); regular(path); if (read(path).lease === lease) unlinkSync(path); };
    } catch (e) {
      if (e.code !== 'EEXIST') throw e;
      regular(path);
      if (!told) { ports.stderr.write('pdd try: waiting for the current Try command…\n'); told = true; }
      if (Date.now() >= end) { const e = new Error('The Try is still busy; this command was not sent. If its process stopped, remove its lock before retrying.'); e.localPath = path; throw e; }
      await new Promise(done => { const timer = setTimeout(finish, 100); function finish() { clearTimeout(timer); ports.signal?.removeEventListener('abort', finish); done(); } ports.signal?.addEventListener('abort', finish, {once:true}); });
    }
  }
}
export async function runShim(descriptorPath, argv, givenPorts = {}) {
  const ports = { env: process.env, stdout: process.stdout, stderr: process.stderr, stdin: process.stdin, ...givenPorts };
  let release, dispose, usagePath, sessionRoot;
  const controller = new AbortController();
  ports.signal = ports.signal ? AbortSignal.any([ports.signal, controller.signal]) : controller.signal;
  const interrupt = () => controller.abort();
  if (givenPorts.onInterrupt) dispose = givenPorts.onInterrupt(interrupt);
  else { process.on('SIGINT', interrupt); dispose = () => process.off('SIGINT', interrupt); }
  try {
    const suffix = /[\/]\.pdd[\/]try[\/]sessions[\/][A-Za-z0-9-]+[\/]door\.json$/;
    const match = resolve(descriptorPath).match(suffix);
    if (!match) fail('No workspace Try record is available. Run pdd try STORY --cli again.');
    const root = resolve(descriptorPath).slice(0, match.index);
    workspaceFile(root, descriptorPath);
    regular(descriptorPath);
    const d = read(descriptorPath);
    if (d.root !== root) fail('The Try record belongs to another workspace.');
    sessionRoot = d.root;
    if (d.version !== 2 || !/^[A-Za-z0-9-]+$/.test(d.sessionId ?? '') || !d.root || realpathSync(d.root) !== d.root) fail('The Try session record is invalid. Run pdd try STORY --cli again.');
    workspaceState(d, descriptorPath);
    usagePath = join(d.stateDir, 'usage.json');
    release = await waitTurn(d, ports);
    const last = join(d.stateDir, 'last.json'), input = { argv };
    privateDir(d.root, d.stateDir);
    writePrivate(last, { state: 'unknown' });
    if (Object.entries(d.promptHashes ?? { [d.prompt]: d.promptHash }).some(([path, expected]) => { const local = resolve(d.root, path); workspaceFile(d.root, local); return hash(readFileSync(local)) !== expected; })) fail('The CLI prompt changed since this Try. Run pdd try STORY --cli --new.');
    if (d.inputSchema.properties?.stdin && !ports.stdin.isTTY) {
      const parts = []; let bytes = 0;
      const collect = async () => { for await (const chunk of ports.stdin) { const part = Buffer.from(chunk); bytes += part.length; if (bytes > 1024 * 1024) fail('Piped stdin exceeds 1 MiB.'); parts.push(part); } };
      let cancel;
      const cancelled = new Promise((_, reject) => { cancel = () => { ports.stdin.destroy?.(); reject(new Error('Stopped reading stdin; this command was not sent.')); }; ports.signal.addEventListener('abort', cancel, {once:true}); if (ports.signal.aborted) cancel(); });
      try { await Promise.race([collect(), cancelled]); } finally { ports.signal.removeEventListener('abort', cancel); }
      const value = new TextDecoder('utf-8', { fatal: true }).decode(Buffer.concat(parts));
      input.stdin = value;
    } else if (d.inputSchema.required?.includes('stdin')) input.stdin = '';
    // A person at a terminal sees that a slow command still runs; a pipe or an agent gets only the program's output.
    const note = ports.stderr.isTTY ? setTimeout(() => ports.stderr.write(`pdd try: running ${d.name ?? 'the command'} on the Try…\n`), 2000) : null;
    let answer;
    try {
      const direct = ports.env.PDD_TRY_TRANSPORT === 'direct' || (ports.env.PDD_TRY_TRANSPORT !== 'mailbox' && ports.stderr.isTTY);
      answer = direct ? await runDoorCall(d, input, { ...ports, env: { ...ports.env, PDD_STATE_DIR: d.runtimeStateDir } }) : await mailboxCall(d, input, ports);
    } finally { clearTimeout(note); }
    const result = answer.result;
    if (typeof result.stdout !== 'string' || typeof result.stderr !== 'string' || !Number.isInteger(result.exit_code) || result.exit_code < 0 || result.exit_code > 255 || result.exit_code === WRAPPER_EXIT) fail('The prompt must return stdout, stderr and an exit_code from 0–255 except reserved code 125.');
    privateDir(d.root, d.stateDir);
    writePrivate(last, { state: 'confirmed', id: answer.id, input, result, inputWorld: answer.inputWorld, world: answer.world });
    writePrivate(usagePath, answer.usage);
    ports.stdout.write(result.stdout); ports.stderr.write(result.stderr);
    if (ports.env.PDD_TRY_USAGE === '1') ports.stderr.write(`${result.stderr && !result.stderr.endsWith('\n') ? '\n' : ''}${tryUsageLine(answer.usage, { command: true })}\n`);
    return result.exit_code;
  } catch (e) {
    const reason = ['EPERM', 'EACCES'].includes(e.code) && e.path ? `Workspace access blocked for ${JSON.stringify(String(e.path))}. Allow access to this workspace and run pdd try STORY --cli again.` : e.code === 'ENOENT' ? 'No Try session is available. Run pdd try STORY --cli again.'
      : e instanceof TypeError && /encoded data/.test(e.message) ? 'Piped stdin must be UTF-8 text.' : cleanText(e.message || 'The command could not run.');
    const usage = e.tryUsage ?? tryUsage({});
    if (usagePath) { try { privateDir(sessionRoot, dirname(usagePath)); writePrivate(usagePath, usage); } catch {} }
    ports.stderr.write(`pdd try: ${reason}${e.localPath ? ` Lock: ${JSON.stringify(e.localPath)}.` : ''}\n`);
    if (ports.env.PDD_TRY_USAGE === '1') ports.stderr.write(`${tryUsageLine(usage, { command: true })}\n`);
    return WRAPPER_EXIT;
  } finally { try { release?.(); } catch { /* A replaced/removed private path is never followed during cleanup. */ } finally { dispose?.(); } }
}

export async function saveLast({ root, store, identity, ports }) {
  const pointer = store.repo(root).last_door;
  if (!pointer) fail('No last command is available. Run the Try command first.');
  regular(pointer.descriptor); regular(pointer.last);
  const d = read(pointer.descriptor), last = read(pointer.last);
  if (d.root !== root || identity.login !== d.login) fail(`This Try belongs to ${d.login}. Run: gh auth switch -u ${d.login}`);
  if (last.state !== 'confirmed') fail('The last command result is unknown; there is no confirmed output to save.');
  if (last.saved) { ports.stdout.write('The last command is already saved.\n'); return 0; }
  if (hash(readFileSync(join(root, d.storyPath))) !== d.storyHash || Object.entries(d.promptHashes ?? { [d.prompt]: d.promptHash }).some(([path, expected]) => hash(readFileSync(join(root, path))) !== expected)) fail('The Story or prompt changed since this Try. Open a new Try and run the command again.');
  const step = { step_id: `try-${last.id}`, entry_path: d.prompt, operation: d.operation, input: last.input,
    checks: [{ criterion_id: d.criterion, target: 'result', path: '', op: 'equals', value: last.result }] };
  const message = saveDoorCase(root, { id: last.id, name: 'Recorded terminal command', story_path: d.storyPath, original_path: d.originalPath,
    test: { schema_version: 'prompt-runtime.program-scenario.v1', story_path: d.storyPath, criteria: d.criteria, steps: [step] } });
  if (message.startsWith('not added:')) fail(message.slice(11));
  writePrivate(pointer.last, { ...last, saved: true });
  ports.stdout.write(`${message}\n`);
  if (last.inputWorld && Object.keys(last.inputWorld).length) ports.stdout.write('This records observed output. Review the saved-data setup before replaying this case.\n');
  return 0;
}

