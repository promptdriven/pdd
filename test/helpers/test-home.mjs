// Generated from prompts/test/test-home-isolation.prompt.md.
// Import before production modules in focused tests and shared fixtures.
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
]) delete process.env[key];

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
