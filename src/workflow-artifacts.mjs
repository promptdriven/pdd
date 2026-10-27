import { execFile } from 'node:child_process';
import { createHash } from 'node:crypto';
import { constants } from 'node:fs';
import * as fs from 'node:fs/promises';
import { basename, isAbsolute, join, relative, resolve, sep } from 'node:path';

const ROLES = new Set(['prompt', 'story', 'cases', 'implementation', 'tests', 'evidence', 'notes']);
const IDENTITIES = ['runId', 'stageId', 'issueUrl', 'inputRevision'];
const shells = new Set(['sh', 'bash', 'dash', 'zsh', 'fish', 'csh', 'tcsh', 'ksh', 'cmd', 'cmd.exe', 'powershell', 'powershell.exe', 'pwsh', 'pwsh.exe']);
const nonempty = value => typeof value === 'string' && value.trim().length > 0 && !value.includes('\0');
const fail = message => { throw new TypeError(message); };
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);

function closed(value, required, optional = []) {
  if (!object(value) || required.some(key => !Object.hasOwn(value, key))
      || Object.keys(value).some(key => !required.includes(key) && !optional.includes(key))) {
    fail('Invalid workflow artifact schema.');
  }
}

function artifactPath(path) {
  if (!nonempty(path) || isAbsolute(path) || /^[A-Za-z]:/.test(path) || path.includes('\\')
      || path.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git')) {
    fail('Artifact path must be a contained project-relative file.');
  }
}

function fileList(files) {
  if (!Array.isArray(files)) fail('Workflow artifacts must be an array.');
  const paths = new Set();
  for (const file of files) {
    closed(file, ['path', 'sha256', 'role'], ['storage']);
    if (Object.hasOwn(file, 'storage') && (file.storage !== 'run' || !['cases', 'notes', 'evidence'].includes(file.role))) fail('Invalid run artifact storage or role.');
    const identity = `${file.storage ?? 'project'}:${file.path}`;
    artifactPath(file.path);
    if (typeof file.sha256 !== 'string' || !/^[a-fA-F0-9]{64}$/.test(file.sha256)
        || !ROLES.has(file.role) || paths.has(identity)) fail('Invalid or duplicate workflow artifact.');
    paths.add(identity);
  }
}

function commandList(commands) {
  if (!Array.isArray(commands) || !commands.length) fail('Test commands require nonempty argv arrays.');
  for (const argv of commands) {
    if (!Array.isArray(argv) || !argv.length || argv.some(arg => typeof arg !== 'string' || arg.includes('\0'))
        || !nonempty(argv[0]) || /[\s;&|<>`$()]/.test(argv[0])
        || shells.has(basename(argv[0]).toLowerCase())) fail('Test commands must be executable argv, not shell text.');
  }
}

function inside(root, target) {
  const rel = relative(root, target);
  if (!rel || rel === '..' || rel.startsWith('..' + sep) || isAbsolute(rel)) fail('File is outside its selected directory.');
  return rel;
}

async function directory(path, io) {
  const selected = resolve(path);
  const stat = await io.lstat(selected);
  if (!stat.isDirectory() || stat.isSymbolicLink() || await io.realpath(selected) !== selected) {
    fail('Selected directory must have no symlink ancestors.');
  }
  return selected;
}

async function pathStats(root, target, io) {
  const parts = inside(root, target).split(sep);
  const stats = [];
  let current = root;
  for (let index = 0; index < parts.length; index++) {
    current = join(current, parts[index]);
    const stat = await io.lstat(current);
    if (stat.isSymbolicLink() || (index === parts.length - 1 ? !stat.isFile() : !stat.isDirectory())) {
      fail('Workflow files and their ancestors must be regular, without symlinks.');
    }
    stats.push(stat);
  }
  return stats;
}

const sameFile = (a, b) => a.dev === b.dev && a.ino === b.ino;
const unchanged = (a, b) => sameFile(a, b) && a.size === b.size && a.mtimeMs === b.mtimeMs && a.ctimeMs === b.ctimeMs;

async function readRegular(root, target, io) {
  const before = await pathStats(root, target, io);
  const handle = await io.open(target, constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0));
  try {
    const opened = await handle.stat();
    if (!opened.isFile() || !sameFile(opened, before.at(-1))) fail('Workflow file changed before reading.');
    const bytes = await handle.readFile();
    const after = await pathStats(root, target, io);
    if (!unchanged(opened, await handle.stat()) || !unchanged(opened, after.at(-1))
        || before.some((stat, index) => !sameFile(stat, after[index]))) fail('Workflow file changed while reading.');
    return bytes;
  } finally {
    await handle.close();
  }
}

async function gitDirectory(root, io) {
  const marker = join(root, '.git');
  const stat = await io.lstat(marker);
  if (stat.isSymbolicLink()) fail('Git metadata cannot be a symlink.');
  if (stat.isDirectory()) return directory(marker, io);
  if (!stat.isFile()) fail('Missing regular Git metadata.');
  const text = (await readRegular(root, marker, io)).toString('utf8');
  const match = /^gitdir: ([^\r\n]+)\r?\n?$/.exec(text);
  if (!match) fail('Invalid Git worktree metadata pointer.');
  return directory(resolve(root, match[1]), io);
}

export async function assertWorkflowArtifacts({ cwd, files, artifactDirectory } = {}, ports = {}) {
  fileList(files);
  if (!nonempty(cwd)) fail('A project directory is required.');
  const io = ports.fs ?? fs;
  const root = await directory(cwd, io);
  let runRoot;
  if (files.some(file => file.storage === 'run')) {
    const metadata = await gitDirectory(root, io);
    if (!nonempty(artifactDirectory)) fail('Run artifact directory is required.');
    const rel = inside(metadata, resolve(artifactDirectory)).split(sep);
    if (rel.length !== 4 || rel[0] !== 'pdd' || rel[1] !== 'workflows' || rel[3] !== 'artifacts'
        || !/^[a-zA-Z0-9_-]+$/.test(rel[2])) fail('Invalid run artifact directory.');
    let current = metadata;
    for (const part of rel) current = await directory(join(current, part), io);
    runRoot = current;
  }
  for (const file of files) {
    const selected = file.storage === 'run' ? runRoot : root;
    const bytes = await readRegular(selected, resolve(selected, file.path), io);
    if (createHash('sha256').update(bytes).digest('hex') !== file.sha256.toLowerCase()) {
      fail('Workflow artifact hash does not match actual bytes: ' + file.path);
    }
  }
}

export async function readWorkflowHandoff({ handoffPath, cwd, artifactDirectory, expected, requiredRoles = [] } = {}, ports = {}) {
  closed(expected, IDENTITIES);
  if (IDENTITIES.some(key => !nonempty(expected[key]))) fail('Expected workflow identities are required.');
  if (!Array.isArray(requiredRoles) || requiredRoles.some(role => !ROLES.has(role))
      || new Set(requiredRoles).size !== requiredRoles.length) fail('Invalid required artifact roles.');
  if (!nonempty(cwd) || !nonempty(handoffPath) || handoffPath.includes('\\')
      || handoffPath.split('/').some(part => part === '..' || part === '.')) fail('Invalid handoff location.');
  const io = ports.fs ?? fs;
  const root = await directory(cwd, io);
  const metadata = await gitDirectory(root, io);
  const data = JSON.parse((await readRegular(metadata, resolve(root, handoffPath), io)).toString('utf8'));
  closed(data, ['version', ...IDENTITIES, 'summary', 'files'], ['testCommands']);
  if (data.version !== 1 || !nonempty(data.summary)
      || IDENTITIES.some(key => data[key] !== expected[key])) fail('Workflow handoff identity or version does not match.');
  fileList(data.files);
  if (requiredRoles.some(role => !data.files.some(file => file.role === role))) fail('A required workflow artifact role is missing.');
  if (Object.hasOwn(data, 'testCommands')) commandList(data.testCommands);
  if (data.files.some(file => file.storage === 'run')
      && artifactDirectory !== join(metadata, 'pdd', 'workflows', expected.runId, 'artifacts'))
    fail('Run artifact directory does not match the expected run.');
  await assertWorkflowArtifacts({ cwd: root, files: data.files, artifactDirectory }, ports);
  return data;
}

function execute(executor, file, args, cwd) {
  return new Promise((resolveResult, reject) => {
    const callback = (error, stdout = '', stderr = '') => error
      ? reject(Object.assign(error, { stdout: error.stdout ?? stdout, stderr: error.stderr ?? stderr }))
      : resolveResult({ stdout, stderr });
    try {
      const child = executor(file, args, { cwd }, callback);
      if (child && typeof child.then === 'function') child.then(resolveResult, reject);
    } catch (error) { reject(error); }
  });
}

export async function runWorkflowTestCommands({ cwd, testCommands } = {}, ports = {}) {
  commandList(testCommands);
  if (!nonempty(cwd)) fail('A project directory is required.');
  const root = await directory(cwd, ports.fs ?? fs);
  const executor = ports.execFile ?? execFile;
  const results = [];
  for (const command of testCommands) {
    const argv = [...command];
    let exitCode, stdout = '', stderr = '';
    try {
      const result = await execute(executor, argv[0], argv.slice(1), root);
      if (!object(result)) fail('Test execution did not return an observed result.');
      stdout = String(result?.stdout ?? '');
      stderr = String(result?.stderr ?? '');
      exitCode = Object.hasOwn(result, 'exitCode') ? result.exitCode : Object.hasOwn(result, 'code') ? result.code : 0;
      if (!Number.isInteger(exitCode) || exitCode < 0 || result?.signal) {
        exitCode = null;
        stderr += '\nThe test process did not report a normal exit.';
      }
    } catch (error) {
      exitCode = Number.isInteger(error?.code) && error.code >= 0 && !error.signal ? error.code : null;
      // A thrown operational error with code zero is still a failed execution.
      if (exitCode === 0) exitCode = null;
      stdout = String(error?.stdout ?? '');
      stderr = String(error?.stderr ?? '');
      if (!stderr) stderr = String(error?.message ?? error);
    }
    results.push({ argv, exitCode, stdout, stderr });
  }
  return { passed: results.every(result => result.exitCode === 0), results };
}
