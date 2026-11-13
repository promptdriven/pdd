// Generated from prompts/test/test-home-isolation.prompt.md (sha256: e1491f298a2dfa4e68e9655a056ad9b8167e4a87e294a7bc904b80c47da77382).
// Import before production modules in focused tests. npm test preloads it too.
import { mkdtempSync, realpathSync, rmSync } from 'node:fs';
import os, { tmpdir } from 'node:os';
import { syncBuiltinESMExports } from 'node:module';
import { join } from 'node:path';

const home = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-test-home-')));
process.env.HOME = home;
process.env.USERPROFILE = home;
// An inherited override can escape HOME. Leave these absent so tests that replace
// HOME still exercise the production defaults under their own fixture home.
for (const key of [
  'PDD_STATE_DIR', 'XDG_CONFIG_HOME', 'XDG_STATE_HOME', 'XDG_CACHE_HOME',
  'XDG_DATA_HOME', 'XDG_RUNTIME_DIR', 'CODEX_HOME', 'CLAUDE_CONFIG_DIR',
  'GEMINI_CLI_HOME', 'AGY_HOME', 'GH_CONFIG_DIR',
  // Outer suite controls must not select a test's queue or subprocess command.
  'PDD_SUITE_QUEUE', 'PDD_VM_SUITE_LOCK', 'SUITE',
]) delete process.env[key];

// Native tests and their children must never join the caller's live sessions.
// Tests can install their own synthetic selectors after this bootstrap.
for (const key of Object.keys(process.env)) {
  if (/^(?:HERDR_|PDD_AGENT_SESSION$|PDD_AUTOPILOT_CONTEXT$|CLAUDECODE$|CLAUDE_CODE_|CLAUDE_PID$|CODEX_THREAD_ID$|CODEX_SANDBOX)/.test(key)) delete process.env[key];
}

// userInfo bypasses HOME and reads the account database. A caught lookup still
// fails the process; tests of this fallback must supply the existing userInfo port.
let accountHomeRead = false;
os.userInfo = () => {
  accountHomeRead = true;
  throw Object.assign(new Error('PDD_TEST_ACCOUNT_HOME'), { code: 'PDD_TEST_ACCOUNT_HOME' });
};
syncBuiltinESMExports();

// A child that inherits HOME does not import this module unless it is itself a
// test. Only this process removes the home it allocated.
process.once('exit', () => {
  rmSync(home, { recursive: true, force: true });
  if (accountHomeRead) {
    process.stderr.write('PDD_TEST_ACCOUNT_HOME: inject a userInfo fake.\n');
    process.exitCode ||= 1;
  }
});
