import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
import path from 'node:path';

// Portable when copied into test/; external proof selects the source root explicitly.
const root = process.env.PDD_HELP_SOURCE_ROOT || fileURLToPath(new URL('../', import.meta.url));
const runHelp = args => spawnSync(process.execPath, [path.join(root, 'bin/pdd.mjs'), ...args], {encoding: 'utf8', timeout: 10000});

test('public approval help keeps root overview concise and shows full person-relay heredocs in focused help', () => {
  const rootHelp = runHelp(['--help']);
  assert.equal(rootHelp.error, undefined, 'CLI root help must execute');
  assert.equal(rootHelp.status, 0, rootHelp.stderr);
  assert.match(rootHelp.stdout, /^\s+pdd approve PROMPT\b/m, 'approve must appear in root help');
  assert.match(rootHelp.stdout, /^\s+pdd workflow approve \[ISSUE\]/m, 'workflow approve must appear in root help');
  assert.doesNotMatch(rootHelp.stdout, /<<'PDD_SAID'/, 'root help must not duplicate approval heredocs');

  const workflowApprove = runHelp(['workflow', 'approve', '--help']);
  assert.equal(workflowApprove.error, undefined, 'workflow approve help must execute');
  assert.equal(workflowApprove.status, 0, workflowApprove.stderr);
  const line = workflowApprove.stdout.split('\n').find(row => /^\s+pdd workflow approve /.test(row));
  assert.ok(line, 'workflow approve must appear in focused help');
  assert.doesNotMatch(line, /no-said keeps terminal\/native-chat approval|or use terminal\/native area-chat approval/i, 'help must not advertise independent native-chat approval');
  assert.match(line, /--said/);
  assert.match(line, /gate.*all.*draft/i);
  for (const out of [workflowApprove.stdout, runHelp(['approve', '--help']).stdout]) {
    assert.match(out, /nonblank|non-empty|nonempty/i);
    assert.match(out, /any chat/i);
    assert.match(out, /without grading|does not grade|no grading/i);
    assert.match(out, /ask.*person/i);
    assert.match(out, /agent/i);
    assert.match(out, /ask the person[.;,]? then relay their words with --said/i);
    assert.match(out, /without --said, use a separate person terminal/i);
    assert.doesNotMatch(out, /non-TTY|current[- ]area[- ]pane/i);
    assert.match(out, /terminal y\/N/i);
    assert.match(out, /strict_approvals.*terminal/i);
    assert.match(out, /trailing newlines/i);
    assert.match(out, /delimiter absent/i);
  }
  assert.ok(workflowApprove.stdout.includes("pdd workflow approve N --said - <<'PDD_SAID'\n"));
  const promptApprove = runHelp(['approve', '--help']);
  assert.equal(promptApprove.status, 0, promptApprove.stderr);
  assert.ok(promptApprove.stdout.includes("pdd approve PATH --said - <<'PDD_SAID'\n"));
});
