import test from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
import path from 'node:path';

// Portable when copied into test/; external proof selects the source root explicitly.
const root = process.env.PDD_HELP_SOURCE_ROOT || fileURLToPath(new URL('../', import.meta.url));
test('public workflow approval help requires explicit person relay or person terminal', () => {
  const result = spawnSync(process.execPath, [path.join(root, 'bin/pdd.mjs'), '--help'], {encoding: 'utf8', timeout: 10000});
  assert.equal(result.error, undefined, 'CLI help must execute');
  assert.equal(result.status, 0, result.stderr);
  const line = result.stdout.split('\n').find(row => /^\s+pdd workflow approve /.test(row));
  assert.ok(line, 'workflow approve must appear in public help');
  assert.doesNotMatch(line, /no-said keeps terminal\/native-chat approval|or use terminal\/native area-chat approval/i, 'help must not advertise independent native-chat approval');
  assert.match(line, /--said/);
  assert.match(line, /gate.*all.*draft/i);
  assert.match(result.stdout, /nonblank|non-empty|nonempty/i);
  assert.match(result.stdout, /any chat/i);
  assert.match(result.stdout, /without grading|does not grade|no grading/i);
  assert.match(result.stdout, /ask.*person/i);
  assert.match(result.stdout, /agent/i);
  assert.match(result.stdout, /non-TTY/i);
  assert.match(result.stdout, /current area pane|current-area-pane/i);
  assert.match(result.stdout, /terminal y\/N/i);
  assert.match(result.stdout, /strict_approvals.*terminal/i);
  assert.ok(result.stdout.includes("pdd workflow approve N --said - <<'PDD_SAID'\n"));
  assert.ok(result.stdout.includes("pdd approve PATH --said - <<'PDD_SAID'\n"));
  assert.match(result.stdout,/trailing newlines/i);
  assert.match(result.stdout,/delimiter absent/i);
});
