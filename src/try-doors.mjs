// Generated from prompts/cli/try-doors.prompt.md (sha256: b42664022db320fcbb75e16769678cc1abf680de8883f47885b6bc3913c99914).
import { spawn } from 'node:child_process';
import { createHash } from 'node:crypto';
import { accessSync, chmodSync, closeSync, constants, existsSync, lstatSync, mkdirSync, openSync, readFileSync, realpathSync, renameSync, writeFileSync } from 'node:fs';
import { basename, dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { readPrompt } from './runtime-preflight.mjs';
import { cleanText } from './runtime-output.mjs';
import { runDoorCall, saveDoorCase } from './runtime-client.mjs';

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
function writePrivate(path, value) {
  if (existsSync(path)) regular(path);
  const temp = `${path}.${process.pid}.tmp`;
  const fd = openSync(temp, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | constants.O_NOFOLLOW, 0o600);
  try { writeFileSync(fd, JSON.stringify(value, null, 2) + '\n'); } finally { closeSync(fd); }
  renameSync(temp, path);
}
function safeBin(root) {
  let path = root;
  for (const part of ['.pdd', 'try', 'bin']) {
    path = join(path, part);
    try { mkdirSync(path, { mode: 0o700 }); } catch (e) { if (e.code !== 'EEXIST') throw e; }
    const stat = lstatSync(path);
    if (stat.isSymbolicLink()) fail(`Refusing a symbolic link at ${part}.`);
    if (!stat.isDirectory()) fail(`${part} is not a folder.`);
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
  const bin = safeBin(root), shim = join(bin, name);
  if (existsSync(shim)) {
    regular(shim);
    if (!readFileSync(shim, 'utf8').startsWith(`#!/bin/sh\n# PDD Try launcher v1\n`)) fail(`Refusing to overwrite ${shim}; it is not a PDD Try launcher.`);
  } else { try { lstatSync(shim); fail('Refusing a symbolic link in Try files.'); } catch (e) { if (e.code !== 'ENOENT') throw e; } }
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
  const descriptorPath = join(store.folder('tries'), `${sessionId}.door.json`);
  if (existsSync(descriptorPath) && read(descriptorPath).promptHash !== hash(prompt.text)) fail('The CLI prompt changed since this Try. Run pdd try STORY --cli --new.');
  const ghPath = (ports.env.PATH || process.env.PATH || '').split(':').map(folder => join(folder, 'gh')).find(path => { try { accessSync(path, constants.X_OK); return (lstatSync(path).isFile() || lstatSync(path).isSymbolicLink()) && !readFileSync(path).subarray(0, 64).toString().includes('PDD Try launcher v1'); } catch { return false; } });
  const descriptor = { version: 1, root, sessionId, origin, login: identity.login, prompt: step.entry_path, operation: step.operation,
    ghPath: ghPath ? resolve(ghPath) : null, promptHashes: record.prompt_hashes, name, inputSchema: entry.input_schema, originalPath: test.path, storyPath: test.doc.story_path, criteria: test.doc.criteria,
    criterion: step.checks[0]?.criterion_id, storyHash: hash(readFileSync(join(root, test.doc.story_path))),
    promptHash: hash(prompt.text), stateDir: store.dir, repoState: join(store.folder('repos'), `${store.repoKey(root)}.json`) };
  writePrivate(descriptorPath, descriptor);
  const moduleUrl = pathToFileURL(join(dirname(fileURLToPath(import.meta.url)), 'try-doors.mjs')).href;
  const script = `import(${JSON.stringify(moduleUrl)}).then(async ({ runShim }) => { process.exitCode = await runShim(${JSON.stringify(descriptorPath)}, process.argv.slice(1)); }).catch(() => { process.stderr.write('pdd try: The installed adapter could not load. Run pdd try STORY --cli again.\\n'); process.exitCode = 125; });`;
  const code = `#!/bin/sh\n# PDD Try launcher v1\nexec ${quote(process.execPath)} --input-type=commonjs -e ${quote(script)} -- \"$@\"\n`;
  const fd = openSync(shim, constants.O_WRONLY | constants.O_CREAT | constants.O_TRUNC | constants.O_NOFOLLOW, 0o700);
  try { writeFileSync(fd, code); } finally { closeSync(fd); }
  chmodSync(shim, 0o700);
  ports.stdout.write(`Try is ready: ${name}\n${shim}\nexport PATH=${quote(bin)}:"$PATH"\n`);
  const examples = [...new Set(test.doc.steps.filter(s => s.entry_path === step.entry_path && s.operation === step.operation && Array.isArray(s.input?.argv))
    .map(s => [name, ...s.input.argv].map(quote).join(' ')))];
  if (examples.length) ports.stdout.write(`Examples from this Story:\n${examples.map(s => `  ${s}`).join('\n')}\n`);
  if (options['--shell']) {
    const chosen = ports.env.SHELL || '/bin/sh', shell = ['bash', 'zsh', 'sh'].includes(basename(chosen)) ? chosen : '/bin/sh';
    const env = { ...ports.env, PATH: `${bin}:${ports.env.PATH || process.env.PATH || ''}` };
    if (ports.shell) return ports.shell(shell, env);
    return new Promise((done, reject) => { const child = spawn(shell, ['-i'], { cwd: root, env, stdio: 'inherit' }); child.on('error', reject); child.on('exit', (code, signal) => done(code ?? (signal ? 128 : 0))); });
  }
  return 0;
}

function invalidate(descriptor, path) {
  const last = join(dirname(path), `${descriptor.sessionId}.last.json`);
  writePrivate(last, { state: 'unknown' });
  regular(descriptor.repoState);
  writePrivate(descriptor.repoState, { ...read(descriptor.repoState), last_door: { descriptor: path, last } });
  return last;
}
export async function runShim(descriptorPath, argv, givenPorts = {}) {
  const ports = { env: process.env, stdout: process.stdout, stderr: process.stderr, stdin: process.stdin, ...givenPorts };
  try {
    regular(descriptorPath);
    const d = read(descriptorPath);
    if (d.version !== 1 || !d.sessionId || !d.root || realpathSync(d.root) !== d.root) fail('The Try session record is invalid. Run pdd try STORY --cli again.');
    const last = invalidate(d, descriptorPath), input = { argv };
    if (Object.entries(d.promptHashes ?? { [d.prompt]: d.promptHash }).some(([path, expected]) => hash(readFileSync(join(d.root, path))) !== expected)) fail('The CLI prompt changed since this Try. Run pdd try STORY --cli --new.');
    if (d.inputSchema.properties?.stdin && !ports.stdin.isTTY) {
      const parts = []; let bytes = 0;
      for await (const chunk of ports.stdin) { const part = Buffer.from(chunk); bytes += part.length; if (bytes > 1024 * 1024) fail('Piped stdin exceeds 1 MiB.'); parts.push(part); }
      const value = new TextDecoder('utf-8', { fatal: true }).decode(Buffer.concat(parts));
      input.stdin = value;
    } else if (d.inputSchema.required?.includes('stdin')) input.stdin = '';
    const answer = await runDoorCall(d, input, { ...ports, ghPath: d.ghPath, env: { ...ports.env, PDD_STATE_DIR: d.stateDir } });
    const result = answer.result;
    if (typeof result.stdout !== 'string' || typeof result.stderr !== 'string' || !Number.isInteger(result.exit_code) || result.exit_code < 0 || result.exit_code > 255 || result.exit_code === WRAPPER_EXIT) fail('The prompt must return stdout, stderr and an exit_code from 0–255 except reserved code 125.');
    writePrivate(last, { state: 'confirmed', id: answer.id, input, result, inputWorld: answer.inputWorld, world: answer.world });
    ports.stdout.write(result.stdout); ports.stderr.write(result.stderr);
    return result.exit_code;
  } catch (e) {
    const reason = e.code === 'ENOENT' ? 'No Try session is available. Run pdd try STORY --cli again.'
      : e instanceof TypeError && /encoded data/.test(e.message) ? 'Piped stdin must be UTF-8 text.' : cleanText(e.message || 'The command could not run.');
    ports.stderr.write(`pdd try: ${reason}\n`); return WRAPPER_EXIT;
  }
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

