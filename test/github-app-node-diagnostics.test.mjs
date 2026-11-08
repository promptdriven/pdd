import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { join } from 'node:path';
import { mkdirSync, writeFileSync } from 'node:fs';
import { nativeGithubCounter } from '../src/github-calls.mjs';
import { githubAppEnvironment } from '../src/github-app.mjs';
import { githubAppWorld } from './helpers/github-app-world.mjs';
const execute = promisify(execFile);

for (const route of ['native', 'gh', 'git']) for (const debug of ['', 'child_process', '*']) {
  test(`App ${route} protects spawning Node diagnostics: ${debug || 'disabled'}`, async t => {
    const w = await githubAppWorld(t);
    w.time = Date.now();
    const seed = nativeGithubCounter(async (file, args, options) => file === 'git'
      ? execute(file, args, options) : { code: 0, stdout: '', stderr: '' },
      { env: w.env, stateRoot: w.stateRoot, now: () => w.time, appPorts: w.appPorts });
    await seed('gh', ['api', 'rate_limit'], { cwd: w.cwd, env: w.env });
    const bin = join(w.dir, 'debug-bin'); mkdirSync(bin);
    const git = execFileSync('which', ['git'], { encoding: 'utf8' }).trim();
    writeFileSync(join(bin, 'gh'), '#!/bin/sh\nprintf safe-output\n', { mode: 0o755 });
    writeFileSync(join(bin, 'git'), `#!/bin/sh\ncase "$1" in remote|config) exec '${git}' "$@";; esac\nprintf safe-output\n`, { mode: 0o755 });
    const env = { ...w.env, PATH: `${bin}:${w.env.PATH}`, NODE_DEBUG: debug };
    const appEnv = githubAppEnvironment({ root: w.cwd, env });
    let file = route, args = route === 'git' ? ['ls-remote', 'https://github.com/acme/widgets'] : ['api', 'repos/acme/widgets'];
    if (route === 'native') {
      file = process.execPath;
      args = ['--input-type=module', '-e', `
        import {execFile} from 'node:child_process';
        import {promisify} from 'node:util';
        import {nativeGithubCounter} from ${JSON.stringify(new URL('../src/github-calls.mjs', import.meta.url).href)};
        try { const r = await nativeGithubCounter(promisify(execFile))('gh', ['api','repos/acme/widgets'], {cwd:process.cwd(),env:process.env}); process.stdout.write(r.stdout); }
        catch(e) {process.stderr.write(String(e.code));process.exitCode=1;}
      `];
    }
    const result = await execute(file, args, { cwd: w.cwd, env: { ...env, ...appEnv }, encoding: 'utf8' })
      .then(r => ({ ...r, code: 0 }), e => ({ stdout: e.stdout ?? '', stderr: e.stderr ?? '', code: e.code }));
    const containsSecret = w.tokens.some(token => `${result.stdout}${result.stderr}`.includes(token)
      || `${result.stdout}${result.stderr}`.includes(Buffer.from(`x-access-token:${token}`).toString('base64')));
    assert.equal(containsSecret, false, 'no raw or encoded installation credential in process output');
    assert.equal(result.code, debug ? 1 : 0);
    if (!debug) assert.equal(result.stdout, 'safe-output');
  });
}
