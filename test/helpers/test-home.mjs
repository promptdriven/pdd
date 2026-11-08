// Generated from prompts/test/test-home-isolation.prompt.md.
// Import before production modules in focused tests. npm test preloads it too.
import fs, { mkdtempSync, realpathSync, rmSync } from 'node:fs';
import promises from 'node:fs/promises';
import os, { tmpdir } from 'node:os';
import { syncBuiltinESMExports } from 'node:module';
import { join, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';

const home = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-test-home-')));
process.env.HOME = home;
process.env.USERPROFILE = home;
process.env.PDD_INTERPRETER_QUEUE = join(home, 'interpreter-queue');
// An inherited override can escape HOME. Leave these absent so tests that replace
// HOME still exercise the production defaults under their own fixture home.
for (const key of [
  'PDD_STATE_DIR', 'XDG_CONFIG_HOME', 'XDG_STATE_HOME', 'XDG_CACHE_HOME',
  'XDG_DATA_HOME', 'XDG_RUNTIME_DIR', 'CODEX_HOME', 'CLAUDE_CONFIG_DIR',
  'GEMINI_CLI_HOME', 'AGY_HOME', 'GH_CONFIG_DIR',
]) delete process.env[key];

// userInfo bypasses HOME and reads the account database. A caught lookup still
// fails the process; tests of this fallback must supply the existing userInfo port.
let accountHomeRead = false;
os.userInfo = () => {
  accountHomeRead = true;
  throw Object.assign(new Error('PDD_TEST_ACCOUNT_HOME'), { code: 'PDD_TEST_ACCOUNT_HOME' });
};
// The machine queue is independent of HOME and TMPDIR. Refuse before I/O even
// when a fixture replaces its environment and drops the private selector.
const machineQueue = `/tmp/pdd-interpreter-${process.getuid?.() ?? 'user'}`;
let machineQueueAccess = false;
function guardQueue(path) {
  if (typeof path !== 'string' && !Buffer.isBuffer(path) && !(path instanceof URL)) return;
  const value = resolve(path instanceof URL ? fileURLToPath(path) : String(path));
  if (value !== machineQueue && !value.startsWith(machineQueue + sep)) return;
  machineQueueAccess = true;
  throw Object.assign(new Error('PDD_TEST_INTERPRETER_QUEUE'), { code: 'PDD_TEST_INTERPRETER_QUEUE' });
}
for (const [port, names] of [
  [fs, ['accessSync', 'access', 'existsSync', 'lstatSync', 'lstat', 'statSync', 'stat',
    'readFileSync', 'readFile', 'openSync', 'open', 'readdirSync', 'readdir',
    'mkdirSync', 'mkdir', 'writeFileSync', 'writeFile', 'appendFileSync', 'appendFile',
    'unlinkSync', 'unlink', 'rmSync', 'rm', 'rmdirSync', 'rmdir',
    'renameSync', 'rename', 'copyFileSync', 'copyFile', 'cpSync', 'cp',
    'symlinkSync', 'symlink', 'linkSync', 'link', 'createReadStream', 'createWriteStream',
    'opendirSync', 'opendir', 'realpathSync', 'realpath', 'readlinkSync', 'readlink',
    'truncateSync', 'truncate', 'mkdtempSync', 'mkdtemp', 'chmodSync', 'chmod',
    'chownSync', 'chown', 'lchownSync', 'lchown', 'lchmodSync', 'lchmod',
    'utimesSync', 'utimes', 'lutimesSync', 'lutimes', 'statfsSync', 'statfs',
    'watch', 'watchFile', 'unwatchFile']],
  [promises, ['access', 'lstat', 'stat', 'readFile', 'open', 'readdir', 'mkdir',
    'writeFile', 'appendFile', 'unlink', 'rm', 'rmdir', 'rename', 'copyFile', 'cp', 'symlink', 'link',
    'opendir', 'realpath', 'readlink', 'truncate', 'mkdtemp', 'chmod', 'chown',
    'lchown', 'lchmod', 'utimes', 'lutimes', 'statfs', 'watch']],
]) for (const name of names) {
  const original = port[name];
  if (typeof original !== 'function') continue;
  const twoPaths = /^(?:rename|copyFile|cp|symlink|link)/.test(name);
  port[name] = function(path, ...args) {
    guardQueue(path);
    if (twoPaths) guardQueue(args[0]);
    return original.call(this, path, ...args);
  };
  if (typeof original.native === 'function') port[name].native = function(path, ...args) {
    guardQueue(path);
    return original.native.call(this, path, ...args);
  };
}
syncBuiltinESMExports();

// A child that inherits HOME does not import this module unless it is itself a
// test. Only this process removes the home it allocated.
process.once('exit', () => {
  rmSync(home, { recursive: true, force: true });
  if (machineQueueAccess) {
    process.stderr.write('PDD_TEST_INTERPRETER_QUEUE: supply a temporary queue.\n');
    process.exitCode ||= 1;
  }
  if (accountHomeRead) {
    process.stderr.write('PDD_TEST_ACCOUNT_HOME: inject a userInfo fake.\n');
    process.exitCode ||= 1;
  }
});
