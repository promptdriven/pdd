// Preload only in isolated test children. Refuse before opening host account files.
import fs from 'node:fs';
import promises from 'node:fs/promises';
import {syncBuiltinESMExports} from 'node:module';
import {homedir} from 'node:os';
import {join, resolve, sep} from 'node:path';
import {fileURLToPath} from 'node:url';

const home = homedir();
const folders = ['.codex', '.claude', '.gemini', '.config/pdd'].map(dir => join(home, dir));
const files = ['config.toml', 'auth.json', '.claude.json'].map(name => join(home, name));
function guard(path) {
  if (typeof path !== 'string' && !Buffer.isBuffer(path) && !(path instanceof URL)) return;
  const value = resolve(path instanceof URL ? fileURLToPath(path) : String(path));
  if (files.includes(value) || folders.some(dir => value === dir || value.startsWith(dir + sep))) {
    process.stderr.write('HOST_ACCOUNT_READ_BLOCKED\n');
    process.exitCode = 91;
    throw Object.assign(Error('Host account access blocked before I/O'), {code:'HOST_ACCOUNT_READ_BLOCKED'});
  }
}
for (const [port, names] of [[fs, ['readFileSync','readFile','openSync','open','readdirSync','readdir']],
  [promises, ['readFile','open','readdir']]]) {
  for (const name of names) {
    const original = port[name];
    port[name] = function(path, ...args) { guard(path); return original.call(this, path, ...args); };
  }
}
syncBuiltinESMExports();
