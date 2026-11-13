import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, closeSync, existsSync, mkdirSync, mkdtempSync, openSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const sourceRoot = fileURLToPath(new URL('../..', import.meta.url));
const cli = join(sourceRoot, 'bin/pdd.mjs');
const raw = readFileSync(join(sourceRoot, 'test/fixtures/interface-drafting/percent.prompt.md'), 'utf8');
const prose = raw.replace(/<details><summary>Runtime interface<\/summary>[\s\S]*?<\/details>/, '');
const object = properties => ({ type: 'object', properties, required: Object.keys(properties), additionalProperties: false });
const addition = { entries: [{ operation: 'second', input_schema: object({ value: { type: 'number' } }), result_schema: object({ text: { type: 'string' } }), errors: [] }] };

function project(t, files) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-draft-save-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const home = join(root, 'home'), repo = join(root, 'repo');
  mkdirSync(home); mkdirSync(repo);
  const env = { ...process.env, HOME: home, USERPROFILE: home, XDG_CONFIG_HOME: join(home, '.config'), PDD_STATE_DIR: join(home, 'state') };
  for (const [path, content] of Object.entries(files)) {
    mkdirSync(join(repo, path, '..'), { recursive: true });
    writeFileSync(join(repo, path), content);
  }
  for (const args of [['init', '-q'], ['add', '.'], ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid', '-c', 'commit.gpgsign=false', 'commit', '-qm', 'fixture']]) {
    const result = spawnSync('git', args, { cwd: repo, env, encoding: 'utf8' });
    assert.equal(result.status, 0, result.stderr);
  }
  return { repo, env };
}
function draft(fixture, args, preload) {
  const result = spawnSync(process.execPath, [...(preload ? ['--import', preload] : []), cli, 'interface', 'draft', ...args, '--json'], { cwd: fixture.repo, env: fixture.env, encoding: 'utf8' });
  assert.ifError(result.error);
  assert.equal(result.signal, null, result.stderr);
  return result;
}
function denySave(t, directory, record) {
  chmodSync(directory, 0o555);
  if (record) chmodSync(record, 0o444);
  let denied = false;
  const probe = record ?? join(directory, 'permission-probe');
  try { closeSync(openSync(probe, record ? 'a' : 'wx')); }
  catch (error) { if (!['EACCES', 'EPERM'].includes(error.code)) throw error; denied = true; }
  if (!record) rmSync(probe, { force: true });
  if (!denied) t.skip('This account or filesystem bypasses write permissions.');
  return denied;
}
function partialWrite(fixture, target) {
  const preload = join(fixture.env.HOME, 'partial-write.mjs');
  writeFileSync(preload, `import fs from 'node:fs';
import { dirname, basename, join } from 'node:path';
import { syncBuiltinESMExports } from 'node:module';
const original = fs.writeFileSync, root = ${JSON.stringify(fixture.repo)}, target = ${JSON.stringify(target)};
let fired = false;
fs.writeFileSync = (path, data, ...args) => {
  const selected = target === 'provenance'
    ? dirname(String(path)) === join(root, '.pdd') && basename(String(path)) !== '.gitignore'
    : String(path) === join(root, target) || (basename(String(path)) === 'next' && dirname(dirname(String(path))) === dirname(join(root, target)) && basename(dirname(String(path))).startsWith('.pdd-' + basename(target).slice(0,32) + '-'));
  if (selected && !fired) {
    fired = true;
    original(path, Buffer.from(data).subarray(0, 16), ...args);
    throw Object.assign(new Error('ENOSPC: injected partial write'), { code: 'ENOSPC' });
  }
  return original(path, data, ...args);
};
syncBuiltinESMExports();
`);
  return preload;
}

test('failed new-draft provenance save leaves prompt bytes untouched (AC1)', t => {
  const fixture = project(t, { 'prompts/percent.prompt.md': prose });
  const directory = join(fixture.repo, '.pdd'), record = join(directory, 'interface-drafts.json');
  mkdirSync(directory); writeFileSync(join(directory, '.gitignore'), '*\n');
  try {
    if (!denySave(t, directory)) return;
    const result = draft(fixture, ['prompts/percent.prompt.md']);
    assert.equal(result.status, 2, result.stdout + result.stderr);
    assert.match(result.stderr, /EACCES|EPERM/);
    assert.equal(existsSync(record), false, 'FAILED_NEW_SAVE_CREATED_PROVENANCE');
    assert.deepEqual(readdirSync(directory), ['.gitignore'], 'FAILED_NEW_SAVE_LEFT_TEMPORARY_PROVENANCE');
    assert.equal(readFileSync(join(fixture.repo, 'prompts/percent.prompt.md'), 'utf8'), prose, 'FAILED_NEW_SAVE_MUTATED_PROMPT');
  } finally { chmodSync(directory, 0o755); }
});

test('failed extension provenance save preserves approved prompt and prior records (AC2)', t => {
  const fixture = project(t, { 'prompts/percent.prompt.md': raw, 'prompts/other.prompt.md': prose, 'contracts/add.json': JSON.stringify(addition) });
  const seed = draft(fixture, ['prompts/other.prompt.md']);
  assert.equal(seed.status, 0, seed.stdout + seed.stderr);
  const other = readFileSync(join(fixture.repo, 'prompts/other.prompt.md'), 'utf8');
  const directory = join(fixture.repo, '.pdd'), record = join(directory, 'interface-drafts.json');
  const beforeRecords = readFileSync(record, 'utf8');
  try {
    if (!denySave(t, directory, record)) return;
    const result = draft(fixture, ['prompts/percent.prompt.md', '--extend', '--contract', 'contracts/add.json']);
    assert.equal(result.status, 2, result.stdout + result.stderr);
    assert.match(result.stderr, /EACCES|EPERM/);
    assert.equal(readFileSync(record, 'utf8'), beforeRecords, 'FAILED_EXTENSION_SAVE_CHANGED_PRIOR_RECORDS');
    assert.equal(readFileSync(join(fixture.repo, 'prompts/other.prompt.md'), 'utf8'), other, 'FAILED_EXTENSION_CHANGED_UNSELECTED_PROMPT');
    assert.equal(readFileSync(join(fixture.repo, 'prompts/percent.prompt.md'), 'utf8'), raw, 'FAILED_EXTENSION_SAVE_MUTATED_APPROVED_PROMPT');
  } finally { chmodSync(directory, 0o755); chmodSync(record, 0o644); }
});

test('independent validation refusal preserves successful draft and provenance (AC3)', t => {
  const malformed = '# Invalid\n\n<details><summary>Runtime interface</summary>\nnot a JSON block\n</details>\n';
  for (const badName of ['a-invalid', 'z-invalid']) {
    const invalid = `prompts/${badName}.prompt.md`, valid = 'prompts/percent.prompt.md';
    const fixture = project(t, { [invalid]: malformed, [valid]: prose });
    const result = draft(fixture, ['--all']);
    assert.equal(result.status, 4, result.stdout + result.stderr);
    const report = JSON.parse(result.stdout);
    assert.equal(report.exit_code, 4);
    assert.equal(report.rows.find(row => row.path === invalid).state, 'refused');
    assert.equal(report.rows.find(row => row.path === valid).state, 'drafted');
    assert.equal(report.rows.find(row => row.path === valid).lint_clean, true);
    assert.equal(readFileSync(join(fixture.repo, invalid), 'utf8'), malformed);
    const saved = readFileSync(join(fixture.repo, valid), 'utf8');
    assert.notEqual(saved, prose);
    assert.ok(saved.includes('"operation": "formatPercent"'));
    assert.ok(saved.includes('"status": "draft"'));
    const records = JSON.parse(readFileSync(join(fixture.repo, '.pdd/interface-drafts.json'), 'utf8'));
    assert.deepEqual(Object.keys(records), [valid]);
    assert.equal(typeof records[valid].interface_sha256, 'string');
  }
});

test('failed shared provenance save restores every affected prompt (AC1, AC2)', t => {
  const fixture = project(t, { 'prompts/first.prompt.md': prose, 'prompts/second.prompt.md': prose });
  const directory = join(fixture.repo, '.pdd');
  mkdirSync(directory); writeFileSync(join(directory, '.gitignore'), '*\n');
  try {
    if (!denySave(t, directory)) return;
    const result = draft(fixture, ['--all']);
    assert.equal(result.status, 2, result.stdout + result.stderr);
    assert.match(result.stderr, /EACCES|EPERM/);
    for (const path of ['prompts/first.prompt.md', 'prompts/second.prompt.md']) {
      assert.equal(readFileSync(join(fixture.repo, path), 'utf8'), prose, 'FAILED_BATCH_SAVE_MUTATED_PROMPT');
    }
    assert.equal(existsSync(join(directory, 'interface-drafts.json')), false);
  } finally { chmodSync(directory, 0o755); }
});

test('partial provenance write preserves prior records and approved prompt (AC2)', t => {
  const fixture = project(t, { 'prompts/percent.prompt.md': raw, 'prompts/other.prompt.md': prose, 'contracts/add.json': JSON.stringify(addition) });
  const seed = draft(fixture, ['prompts/other.prompt.md']);
  assert.equal(seed.status, 0, seed.stdout + seed.stderr);
  const directory = join(fixture.repo, '.pdd'), record = join(directory, 'interface-drafts.json');
  const before = readFileSync(record);
  const result = draft(fixture, ['prompts/percent.prompt.md', '--extend', '--contract', 'contracts/add.json'], partialWrite(fixture, 'provenance'));
  assert.equal(result.status, 2, result.stdout + result.stderr);
  assert.match(result.stderr, /ENOSPC: injected partial write/);
  assert.deepEqual(readFileSync(record), before, 'PARTIAL_SAVE_CHANGED_PRIOR_RECORDS');
  assert.equal(readFileSync(join(fixture.repo, 'prompts/percent.prompt.md'), 'utf8'), raw, 'PARTIAL_SAVE_MUTATED_APPROVED_PROMPT');
  assert.deepEqual(readdirSync(directory).sort(), ['.gitignore', 'interface-drafts.json']);
});

test('partial prompt write restores refused row without saving false provenance (AC3)', t => {
  for (const failed of ['prompts/a-failed.prompt.md', 'prompts/z-failed.prompt.md']) {
    const valid = 'prompts/percent.prompt.md';
    const fixture = project(t, { [failed]: prose, [valid]: prose });
    const result = draft(fixture, ['--all'], partialWrite(fixture, failed));
    assert.equal(result.status, 4, result.stdout + result.stderr);
    const report = JSON.parse(result.stdout);
    assert.equal(report.rows.find(row => row.path === failed).state, 'refused');
    assert.equal(report.rows.find(row => row.path === failed).problems[0].code, 'ENOSPC');
    assert.equal(report.rows.find(row => row.path === valid).state, 'drafted');
    assert.equal(readFileSync(join(fixture.repo, failed), 'utf8'), prose, 'PARTIAL_PROMPT_WRITE_NOT_RESTORED');
    assert.notEqual(readFileSync(join(fixture.repo, valid), 'utf8'), prose);
    const records = JSON.parse(readFileSync(join(fixture.repo, '.pdd/interface-drafts.json'), 'utf8'));
    assert.deepEqual(Object.keys(records), [valid], 'FAILED_PROMPT_WRITE_SAVED_FALSE_PROVENANCE');
  }
});

test('read-only provenance in a writable directory still refuses without changing prompt or records (AC2)', t => {
  const fixture = project(t, { 'prompts/percent.prompt.md': raw, 'prompts/other.prompt.md': prose, 'contracts/add.json': JSON.stringify(addition) });
  const seed = draft(fixture, ['prompts/other.prompt.md']);
  assert.equal(seed.status, 0, seed.stdout + seed.stderr);
  const record = join(fixture.repo, '.pdd/interface-drafts.json'), before = readFileSync(record);
  chmodSync(record, 0o444);
  try {
    let denied = false;
    try { closeSync(openSync(record, 'r+')); }
    catch (error) { if (!['EACCES', 'EPERM'].includes(error.code)) throw error; denied = true; }
    if (!denied) { t.skip('This account or filesystem bypasses write permissions.'); return; }
    const result = draft(fixture, ['prompts/percent.prompt.md', '--extend', '--contract', 'contracts/add.json']);
    assert.equal(result.status, 2, result.stdout + result.stderr);
    assert.match(result.stderr, /EACCES|EPERM/);
    assert.deepEqual(readFileSync(record), before, 'READ_ONLY_SAVE_CHANGED_PRIOR_RECORDS');
    assert.equal(readFileSync(join(fixture.repo, 'prompts/percent.prompt.md'), 'utf8'), raw, 'READ_ONLY_SAVE_MUTATED_APPROVED_PROMPT');
    assert.equal(statSync(record).mode & 0o777, 0o444);
  } finally { chmodSync(record, 0o644); }
});

test('successful provenance update preserves existing record permissions', t => {
  const fixture = project(t, { 'prompts/first.prompt.md': prose, 'prompts/second.prompt.md': prose });
  const seed = draft(fixture, ['prompts/first.prompt.md']);
  assert.equal(seed.status, 0, seed.stdout + seed.stderr);
  const record = join(fixture.repo, '.pdd/interface-drafts.json');
  chmodSync(record, 0o640);
  const result = draft(fixture, ['prompts/second.prompt.md']);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.equal(statSync(record).mode & 0o777, 0o640, 'SAVE_CHANGED_PRIOR_RECORD_MODE');
  assert.deepEqual(Object.keys(JSON.parse(readFileSync(record, 'utf8'))).sort(), ['prompts/first.prompt.md', 'prompts/second.prompt.md']);
});

function limitedDraft(t, fixture, args, size) {
  const available = spawnSync('prlimit', ['--version'], { encoding: 'utf8' });
  if (available.error?.code === 'ENOENT') { t.skip('prlimit is unavailable on this system.'); return; }
  assert.ifError(available.error);
  assert.equal(available.status, 0, available.stderr);
  const preload = join(fixture.env.HOME, 'handle-sigxfsz.mjs');
  writeFileSync(preload, "process.on('SIGXFSZ', () => {});\n");
  const result = spawnSync('prlimit', [`--fsize=${size}:${size}`, '--', process.execPath, '--import', preload,
    cli, 'interface', 'draft', ...args, '--json'], { cwd: fixture.repo, env: fixture.env, encoding: 'utf8' });
  assert.ifError(result.error);
  assert.equal(result.signal, null, result.stdout + result.stderr);
  return result;
}

test('persistent native file-size failure leaves approved prompt bytes intact (AC2)', t => {
  const fixture = project(t, { 'prompts/percent.prompt.md': raw, 'contracts/add.json': JSON.stringify(addition) });
  assert.ok(Buffer.byteLength(raw) > 1024, 'The original must exceed the native write limit.');
  const result = limitedDraft(t, fixture, ['prompts/percent.prompt.md', '--extend', '--contract', 'contracts/add.json'], 1024);
  if (!result) return;
  assert.equal(result.status, 4, result.stdout + result.stderr);
  const report = JSON.parse(result.stdout);
  assert.equal(report.rows[0].state, 'refused');
  assert.equal(readFileSync(join(fixture.repo, 'prompts/percent.prompt.md'), 'utf8'), raw, 'PERSISTENT_EFBIG_MUTATED_APPROVED_PROMPT');
  assert.equal(report.rows[0].problems[0].code, 'EFBIG');
  assert.equal(existsSync(join(fixture.repo, '.pdd/interface-drafts.json')), false);
  assert.deepEqual(readdirSync(join(fixture.repo, 'prompts')), ['percent.prompt.md']);
});

test('persistent native provenance failure restores every prompt without rewriting originals (AC1, AC2)', t => {
  // Keep each replacement below the limit so this reaches metadata persistence.
  const declared = '# Draft\n\n```json\n' + raw.match(/```json\n([\s\S]*?)\n```/)[1] + '\n```\n';
  const files = { 'prompts/first.prompt.md': declared, 'prompts/second.prompt.md': declared, 'prompts/seed.prompt.md': prose };
  const fixture = project(t, files);
  const seed = draft(fixture, ['prompts/seed.prompt.md']);
  assert.equal(seed.status, 0, seed.stdout + seed.stderr);
  const seedPrompt = readFileSync(join(fixture.repo, 'prompts/seed.prompt.md'));
  const directory = join(fixture.repo, '.pdd'), record = join(directory, 'interface-drafts.json');
  const saved = JSON.parse(readFileSync(record, 'utf8'));
  saved.unrelated = { retained: 'x'.repeat(12000) };
  writeFileSync(record, JSON.stringify(saved)); chmodSync(record, 0o640);
  const before = readFileSync(record);
  const result = limitedDraft(t, fixture, ['--all'], 4096);
  if (!result) return;
  assert.equal(result.status, 2, result.stdout + result.stderr);
  assert.match(result.stderr, /EFBIG/);
  for (const path of ['prompts/first.prompt.md', 'prompts/second.prompt.md']) {
    assert.equal(readFileSync(join(fixture.repo, path), 'utf8'), declared, 'PERSISTENT_PROVENANCE_FAILURE_MUTATED_PROMPT');
  }
  assert.deepEqual(readFileSync(join(fixture.repo, 'prompts/seed.prompt.md')), seedPrompt);
  assert.deepEqual(readFileSync(record), before, 'PERSISTENT_PROVENANCE_FAILURE_CHANGED_PRIOR_RECORDS');
  assert.equal(statSync(record).mode & 0o777, 0o640);
  assert.deepEqual(readdirSync(directory).sort(), ['.gitignore', 'interface-drafts.json']);
  assert.deepEqual(readdirSync(join(fixture.repo, 'prompts')).sort(), ['first.prompt.md', 'second.prompt.md', 'seed.prompt.md']);
});

test('persistent ENOSPC after shared provenance failure restores all original files (AC1, AC2)', t => {
  const fixture = project(t, { 'prompts/first.prompt.md': prose, 'prompts/second.prompt.md': prose, 'prompts/seed.prompt.md': prose });
  const seed = draft(fixture, ['prompts/seed.prompt.md']);
  assert.equal(seed.status, 0, seed.stdout + seed.stderr);
  const directory = join(fixture.repo, '.pdd'), record = join(directory, 'interface-drafts.json');
  const before = readFileSync(record), seedPrompt = readFileSync(join(fixture.repo, 'prompts/seed.prompt.md'));
  const preload = join(fixture.env.HOME, 'persistent-enospc.mjs');
  writeFileSync(preload, `import fs from 'node:fs';
import { basename, dirname } from 'node:path';
import { syncBuiltinESMExports } from 'node:module';
const original = fs.writeFileSync, directory = ${JSON.stringify(directory)};
let full = false;
fs.writeFileSync = (path, data, ...args) => {
  if (!full && dirname(String(path)) === directory && basename(String(path)).startsWith('interface-drafts-')) {
    full = true;
    original(path, Buffer.from(data).subarray(0, 16), ...args);
  }
  if (full) throw Object.assign(new Error('ENOSPC: persistent data-write refusal'), { code: 'ENOSPC' });
  return original(path, data, ...args);
};
syncBuiltinESMExports();
`);
  const result = draft(fixture, ['--all'], preload);
  assert.equal(result.status, 2, result.stdout + result.stderr);
  assert.match(result.stderr, /ENOSPC: persistent data-write refusal/);
  for (const path of ['prompts/first.prompt.md', 'prompts/second.prompt.md']) {
    assert.equal(readFileSync(join(fixture.repo, path), 'utf8'), prose, 'PERSISTENT_ENOSPC_ROLLBACK_MUTATED_PROMPT');
  }
  assert.deepEqual(readFileSync(join(fixture.repo, 'prompts/seed.prompt.md')), seedPrompt);
  assert.deepEqual(readFileSync(record), before);
  assert.deepEqual(readdirSync(directory).sort(), ['.gitignore', 'interface-drafts.json']);
  assert.deepEqual(readdirSync(join(fixture.repo, 'prompts')).sort(), ['first.prompt.md', 'second.prompt.md', 'seed.prompt.md']);
});

test('private provenance and prompt staging are restrictive before the first data write completes', t => {
  const fixture = project(t, { 'prompts/percent.prompt.md': raw, 'prompts/other.prompt.md': prose, 'contracts/add.json': JSON.stringify(addition) });
  const seed = draft(fixture, ['prompts/other.prompt.md']);
  assert.equal(seed.status, 0, seed.stdout + seed.stderr);
  const directory = join(fixture.repo, '.pdd'), record = join(directory, 'interface-drafts.json');
  chmodSync(directory, 0o755); chmodSync(record, 0o600);
  chmodSync(join(fixture.repo, 'prompts/percent.prompt.md'), 0o600);
  const preload = join(fixture.env.HOME, 'observe-private-staging.mjs');
  writeFileSync(preload, `import fs from 'node:fs';
import { basename, dirname, join } from 'node:path';
import { syncBuiltinESMExports } from 'node:module';
process.umask(0o022);
const original = fs.writeFileSync, directory = ${JSON.stringify(directory)};
fs.writeFileSync = (path, ...args) => {
  const result = original(path, ...args);
  const file = String(path);
  if (dirname(file) === directory && basename(file).startsWith('interface-drafts-') && file.endsWith('.tmp')) {
    process.stderr.write('PROVENANCE_TEMP_MODE ' + (fs.statSync(file).mode & 0o777) + '\\n');
  }
  if (basename(file) === 'next' && basename(dirname(file)).startsWith('.pdd-percent.prompt.md-')) {
    process.stderr.write('PROMPT_TEMP_MODE ' + (fs.statSync(file).mode & 0o777) + '\\n');
    process.stderr.write('PROMPT_BACKUP_MODE ' + (fs.statSync(join(dirname(file), 'original')).mode & 0o777) + '\\n');
    process.stderr.write('PROMPT_STAGE_DIRECTORY_MODE ' + (fs.statSync(dirname(file)).mode & 0o777) + '\\n');
  }
  return result;
};
syncBuiltinESMExports();
`);
  const result = draft(fixture, ['prompts/percent.prompt.md', '--extend', '--contract', 'contracts/add.json'], preload);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.match(result.stderr, /PROVENANCE_TEMP_MODE 384\n/, 'PROVENANCE_TEMP_WIDENS_PRIVATE_MODE');
  assert.match(result.stderr, /PROMPT_TEMP_MODE 384\n/);
  assert.match(result.stderr, /PROMPT_BACKUP_MODE 384\n/);
  assert.match(result.stderr, /PROMPT_STAGE_DIRECTORY_MODE 448\n/);
  assert.equal(statSync(record).mode & 0o777, 0o600);
  assert.equal(statSync(join(fixture.repo, 'prompts/percent.prompt.md')).mode & 0o777, 0o600);
  assert.deepEqual(readdirSync(directory).sort(), ['.gitignore', 'interface-drafts.json']);
  assert.deepEqual(readdirSync(join(fixture.repo, 'prompts')).sort(), ['other.prompt.md', 'percent.prompt.md']);
});

test('read-only prompt refusal preserves independent writable prompt and its permissions (AC3)', t => {
  const failed = 'prompts/a-read-only.prompt.md', valid = 'prompts/percent.prompt.md';
  const fixture = project(t, { [failed]: prose, [valid]: prose });
  const refused = join(fixture.repo, failed), writable = join(fixture.repo, valid);
  chmodSync(refused, 0o444); chmodSync(writable, 0o640);
  try {
    let denied = false;
    try { closeSync(openSync(refused, 'r+')); }
    catch (error) { if (!['EACCES', 'EPERM'].includes(error.code)) throw error; denied = true; }
    if (!denied) { t.skip('This account or filesystem bypasses write permissions.'); return; }
    const result = draft(fixture, ['--all']);
    assert.equal(result.status, 4, result.stdout + result.stderr);
    const report = JSON.parse(result.stdout);
    assert.equal(report.rows.find(row => row.path === failed).state, 'refused');
    assert.match(report.rows.find(row => row.path === failed).problems[0].code, /EACCES|EPERM/);
    assert.equal(report.rows.find(row => row.path === valid).state, 'drafted');
    assert.equal(readFileSync(refused, 'utf8'), prose);
    assert.equal(statSync(refused).mode & 0o777, 0o444);
    assert.notEqual(readFileSync(writable, 'utf8'), prose);
    assert.equal(statSync(writable).mode & 0o777, 0o640);
    assert.deepEqual(Object.keys(JSON.parse(readFileSync(join(fixture.repo, '.pdd/interface-drafts.json'), 'utf8'))), [valid]);
    assert.deepEqual(readdirSync(join(fixture.repo, 'prompts')).sort(), ['a-read-only.prompt.md', 'percent.prompt.md']);
  } finally { chmodSync(refused, 0o644); }
});
