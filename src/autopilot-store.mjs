// Implements prompts/cli/autopilot-store.prompt.md.
import { createRequire } from 'node:module';
import { openFallbackStore } from './autopilot-store-fallback.mjs';
import * as nativeFs from 'node:fs';
import { randomUUID } from 'node:crypto';
import { basename, dirname, join } from 'node:path';

const require = createRequire(import.meta.url);
const BUCKETS = new Set(['control', 'queue', 'runs', 'leases', 'budgets', 'costs', 'events', 'cache', 'alerts']);
const SCHEMA = 1;
const stateName = name => /^[0-9a-f]{20}\.json$/.test(name);
const encode = value => {
  const text = JSON.stringify(value);
  if (text === undefined) throw new TypeError('Machine state requires a JSON value');
  return text;
};

export function openAutopilotStore({ root }, ports = {}) {
  if (ports.openStore) return ports.openStore({ root });
  const fs = ports.fs ?? nativeFs, file = join(root, 'machine.sqlite');
  let DatabaseSync;
  if (Object.hasOwn(ports, 'sqlite')) DatabaseSync = ports.sqlite?.DatabaseSync;
  else try { ({ DatabaseSync } = require('node:sqlite')); } catch (error) {
    if (error.code !== 'ERR_UNKNOWN_BUILTIN_MODULE') throw error;
  }
  fs.mkdirSync(root, { recursive: true, mode: 0o700 });
  const marker = join(root, 'machine-backend');
  if (!fs.existsSync(marker)) {
    const snapshot = fs.existsSync(join(root, 'machine-state.json')), sqlite = fs.existsSync(file);
    if (snapshot && sqlite) throw Error('Conflicting machine state backends');
    const selected = snapshot ? 'snapshot' : sqlite || DatabaseSync ? 'sqlite' : 'snapshot';
    const temp = join(root, `.backend-${randomUUID()}.tmp`);
    try {
      const fd = fs.openSync(temp, 'wx', 0o600);
      try { fs.writeFileSync(fd, selected); fs.fsyncSync(fd); } finally { fs.closeSync(fd); }
      try { fs.linkSync(temp, marker); } catch (error) { if (error.code !== 'EEXIST') throw error; }
      const parent = fs.openSync(root, 'r'); try { fs.fsyncSync(parent); } finally { fs.closeSync(parent); }
    } finally { try { fs.unlinkSync(temp); } catch (error) { if (error.code !== 'ENOENT') throw error; } }
  }
  const backend = fs.readFileSync(marker, 'utf8');
  if (backend === 'snapshot') return openFallbackStore({ root }, ports);
  if (backend !== 'sqlite') throw Error('Unsupported machine state backend');
  if (!DatabaseSync) throw Error('This runtime cannot open existing SQLite machine state');
  // Create privately before SQLite opens it. SQLite sidecars inherit its mode.
  const fd = fs.openSync(file, 'a', 0o600);
  try { fs.fchmodSync(fd, 0o600); fs.fsyncSync(fd); } finally { fs.closeSync(fd); }
  const db = new DatabaseSync(file);
  let active = false;
  const deadline = performance.now() + 5000;
  const pause = new Int32Array(new SharedArrayBuffer(4));
  try {
    for (;;) {
      // journal_mode can return SQLITE_BUSY immediately despite busy_timeout.
      // Bound all initialization attempts by one deadline, including native waits.
      db.exec(`PRAGMA busy_timeout=${Math.max(0, Math.ceil(deadline - performance.now()))}`);
      try {
        if (db.prepare('PRAGMA user_version').get().user_version > SCHEMA) throw Error('Unsupported machine state schema');
        db.exec('PRAGMA journal_mode=WAL; PRAGMA synchronous=FULL; BEGIN IMMEDIATE');
        try {
          if (db.prepare('PRAGMA user_version').get().user_version > SCHEMA) throw Error('Unsupported machine state schema');
          db.exec(`CREATE TABLE IF NOT EXISTS records (
        bucket TEXT NOT NULL, key TEXT NOT NULL, value TEXT NOT NULL,
        PRIMARY KEY (bucket,key)) STRICT;
        CREATE TABLE IF NOT EXISTS journal (
        sequence INTEGER PRIMARY KEY AUTOINCREMENT, bucket TEXT NOT NULL,
        scope TEXT NOT NULL, value TEXT NOT NULL) STRICT;
        CREATE INDEX IF NOT EXISTS journal_scope ON journal(bucket,scope,sequence);
        CREATE TABLE IF NOT EXISTS imports (identity TEXT PRIMARY KEY) STRICT;
        PRAGMA user_version=1; COMMIT`);
        } catch (error) {
          try { db.exec('ROLLBACK'); } catch { /* Preserve the initialization failure. */ }
          throw error;
        }
        break;
      } catch (error) {
        // Extended result codes keep SQLITE_BUSY (5) or SQLITE_LOCKED (6) in the low byte.
        const primary = error.errcode & 0xff, remaining = deadline - performance.now();
        if ((primary !== 5 && primary !== 6) || remaining <= 0) throw error;
        Atomics.wait(pause, 0, 0, Math.min(10, remaining));
      }
    }
    db.exec('PRAGMA busy_timeout=5000');
  } catch (error) { db.close(); throw error; }
  return {
    close() { db.close(); },
    transaction(callback) {
      if (active) throw Error('Nested machine state transaction');
      db.exec('BEGIN IMMEDIATE'); active = true;
      let usable = true;
      const check = (bucket, key, optional = false) => {
        if (!usable) throw Error('Machine state transaction has ended');
        if (!BUCKETS.has(bucket) || !(typeof key === 'string' || (optional && key === undefined))) throw new TypeError('Invalid machine state address');
      };
      const tx = {
        get(bucket, key) { check(bucket, key); const row = db.prepare('SELECT value FROM records WHERE bucket=? AND key=?').get(bucket, key); return row ? JSON.parse(row.value) : undefined; },
        put(bucket, key, value) { check(bucket, key); db.prepare('INSERT INTO records VALUES (?,?,?) ON CONFLICT(bucket,key) DO UPDATE SET value=excluded.value').run(bucket, key, encode(value)); },
        remove(bucket, key) { check(bucket, key); db.prepare('DELETE FROM records WHERE bucket=? AND key=?').run(bucket, key); },
        list(bucket) { check(bucket, undefined, true); return db.prepare('SELECT key,value FROM records WHERE bucket=? ORDER BY key').all(bucket).map(row => ({ key: row.key, value: JSON.parse(row.value) })); },
        append(bucket, scope, value) { check(bucket, scope); return Number(db.prepare('INSERT INTO journal(bucket,scope,value) VALUES (?,?,?)').run(bucket, scope, encode(value)).lastInsertRowid); },
        entries(bucket, scope) { check(bucket, scope, true); return (scope === undefined
          ? db.prepare('SELECT sequence,scope,value FROM journal WHERE bucket=? ORDER BY sequence').all(bucket)
          : db.prepare('SELECT sequence,scope,value FROM journal WHERE bucket=? AND scope=? ORDER BY sequence').all(bucket, scope))
          .map(row => ({ sequence: row.sequence, scope: row.scope, value: JSON.parse(row.value) })); },
        removeEntry(bucket, scope, sequence) { check(bucket, scope); db.prepare('DELETE FROM journal WHERE bucket=? AND scope=? AND sequence=?').run(bucket, scope, sequence); },
        prune(bucket, scope, before) { check(bucket, scope); db.prepare('DELETE FROM journal WHERE bucket=? AND scope=? AND sequence<=?').run(bucket, scope, before); },
        migrate(identity, read, apply) {
          if (!usable) throw Error('Machine state transaction has ended');
          if (typeof identity !== 'string') throw new TypeError('Invalid migration identity');
          if (db.prepare('SELECT 1 FROM imports WHERE identity=?').get(identity)) return;
          const value = read();
          if (value === undefined) return;
          apply(value);
          db.prepare('INSERT INTO imports VALUES (?)').run(identity);
        },
      };
      try {
        const value = callback(tx);
        if (value && typeof value.then === 'function') throw new TypeError('Machine state transactions must be synchronous');
        usable = false;
        db.exec('COMMIT');
        return value;
      } catch (error) {
        usable = false;
        try { db.exec('ROLLBACK'); } catch { /* Preserve the original failure. */ }
        throw error;
      } finally { active = false; }
    },
  };
}

export function withAutopilotStore(root, ports, action) {
  const store = ports.store ?? openAutopilotStore({ root }, ports);
  try { return store.transaction(action); } finally { if (!ports.store) store.close(); }
}

export function machineJson(options, ports = {}) {
  const { root, bucket, key, file } = options;
  const fs = ports.fs ?? nativeFs;
  const run = action => withAutopilotStore(root, ports, tx => {
    tx.migrate(`json:${bucket}:${key}`, () => {
      try { return JSON.parse(fs.readFileSync(file, 'utf8')); }
      catch (error) { if (error.code === 'ENOENT') return undefined; if (error instanceof SyntaxError && Object.hasOwn(options, 'invalidLegacy')) return options.invalidLegacy; throw error; }
    }, value => tx.put(bucket, key, value));
    return action(tx);
  });
  // A write/clear also marks an absent legacy source consumed. This prevents a
  // late old process from restoring a removed completion through import.
  const mark = tx => tx.migrate(`json:${bucket}:${key}`, () => null, () => {});
  const absent = () => !ports.store && !fs.existsSync(join(root, 'machine.sqlite')) && !fs.existsSync(join(root, 'machine-state.json')) && !fs.existsSync(file);
  return {
    read: (fallback = null) => absent() ? fallback : run(tx => { const value = tx.get(bucket, key); return value === undefined ? fallback : value; }),
    write: value => run(tx => { mark(tx); tx.put(bucket, key, value); }),
    update: callback => run(tx => { const value = callback(tx.get(bucket, key) ?? null); mark(tx); tx.put(bucket, key, value); return value; }),
    clear: () => run(tx => { mark(tx); tx.remove(bucket, key); }),
    exists: () => run(tx => tx.get(bucket, key) !== undefined),
  };
}

const control = (file, ports) => machineJson({ root: dirname(file), bucket: 'control', key: basename(file), file }, ports);
export const readAutopilotState = (file, fallback = null, ports = {}) => control(file, ports).read(fallback);
export const saveAutopilotState = (file, value, ports = {}) => control(file, ports).write(value);
export function autopilotStateFiles(root, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  let legacy = [];
  try { legacy = fs.readdirSync(root).filter(stateName); } catch (error) { if (error.code !== 'ENOENT') throw error; }
  // Do not create state merely to list an unused machine.
  if (!ports.store && !fs.existsSync(join(root, 'machine.sqlite')) && !fs.existsSync(join(root, 'machine-state.json'))) return legacy.sort();
  const keys = withAutopilotStore(root, ports, tx => tx.list('control').map(row => row.key).filter(stateName));
  return [...new Set([...legacy, ...keys])].sort();
}
