import fs from 'node:fs';
import child from 'node:child_process';
import http from 'node:http';
import https from 'node:https';
import net from 'node:net';
import {syncBuiltinESMExports} from 'node:module';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
// Observe native effects at their real imported boundaries. Network attempts are
// counted then refused so an accidental dispatch cannot reach a live service.
// Runtime/model zero counts below are implications of zero network dispatches;
// slot zero is an implication of zero network dispatches AND zero native writes.
// These implications cover this native command, not arbitrary external programs.
export function observe({ state, symlinkTarget }) {
  const calls = { runtime: 0, model: 0, auth: 0, slots: 0, history: 0, write: 0, symlink_target_read: 0 };
  const undo = [];
  const patch = (owner, key, wrap) => {
    if (typeof owner[key] !== 'function') return;
    const old = owner[key]; owner[key] = wrap(old); undo.push(() => { owner[key] = old; });
  };
  const pathOf = value => typeof value === 'string' ? resolve(value) : value instanceof URL ? fileURLToPath(value) : '';
  for (const name of ['readFileSync', 'readdirSync', 'statSync', 'lstatSync', 'accessSync', 'realpathSync', 'openSync']) {
    patch(fs, name, old => function(path, ...args) {
      const actual = pathOf(path);
      if (actual === state || actual.startsWith(`${state}/`)) calls.history++;
      if (actual === symlinkTarget && ['readFileSync', 'openSync'].includes(name)) calls.symlink_target_read++;
      if (name === 'openSync' && (typeof args[0] === 'string' ? /[wa+]/.test(args[0]) : !!(args[0] & (fs.constants.O_WRONLY | fs.constants.O_RDWR | fs.constants.O_CREAT)))) calls.write++;
      return Reflect.apply(old, this, [path, ...args]);
    });
  }
  for (const name of ['writeFileSync', 'appendFileSync', 'writeSync', 'renameSync', 'unlinkSync', 'mkdirSync', 'rmSync', 'rmdirSync', 'truncateSync', 'ftruncateSync', 'chmodSync', 'fchmodSync', 'symlinkSync', 'linkSync', 'copyFileSync']) {
    patch(fs, name, old => function(...args) { calls.write++; return Reflect.apply(old, this, args); });
  }
  for (const name of ['spawnSync', 'spawn', 'execSync', 'exec', 'execFileSync', 'execFile', 'fork']) {
    patch(child, name, old => function(command, ...args) {
      // Git discovery is the command's permitted subprocess. Any other program
      // could authenticate or dispatch: record it and refuse that attempt.
      if (String(command) !== 'git') { calls.auth++; throw new Error('Observed unexpected external program'); }
      return Reflect.apply(old, this, [command, ...args]);
    });
  }
  const dispatch = () => { calls.runtime++; calls.model++; calls.slots++; throw new Error('Observed unexpected network dispatch'); };
  for (const owner of [http, https]) for (const key of ['request', 'get']) patch(owner, key, () => dispatch);
  for (const key of ['connect', 'createConnection']) patch(net, key, () => dispatch);
  patch(globalThis, 'fetch', () => dispatch);
  syncBuiltinESMExports();
  return { calls, restore() { for (const restore of undo.reverse()) restore(); syncBuiltinESMExports(); } };
}
export function snapshot(folder) {
  const result = {};
  const walk = relative => {
    for (const name of fs.readdirSync(join(folder, relative))) {
      if (name === '.git') continue;
      const path = join(relative, name), info = fs.lstatSync(join(folder, path));
      if (info.isSymbolicLink()) result[path] = { link: fs.readlinkSync(join(folder, path)) };
      else if (info.isDirectory()) walk(path);
      else result[path] = {bytes:fs.readFileSync(join(folder,path)).toString('base64'),mode:info.mode};
    }
  };
  walk(''); return result;
}

