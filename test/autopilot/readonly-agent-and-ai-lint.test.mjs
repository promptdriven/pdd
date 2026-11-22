import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  CODEX_DISABLED_FEATURES,
  READONLY_PROVIDERS,
  buildReadonlyAgentArgs,
  extractJsonObject,
  redactReadonlyOutput,
  runReadonlyAgent,
  scrubReadonlyEnv,
  validateJsonAgainstSchema,
} from '../../src/shared/readonly-agent.mjs';
import { buildAiLintPrompt, groupAiLintBatches, runAiLint } from '../../src/autopilot/ai-lint.mjs';
import { buildCodexLintPrompt, groupCodexLintBatches, runCodexLint } from '../../src/codex-lint.mjs';

const sink = () => {
  let text = '';
  return { write(chunk) { text += String(chunk); return true; }, get text() { return text; } };
};

test('readonly-agent builds OS read-only sandbox flags for all 4 providers with zero hardcoded models', () => {
  assert.deepEqual(READONLY_PROVIDERS, ['codex', 'claude', 'gemini', 'agy']);

  // 1. codex: --sandbox read-only, --ignore-rules, disabled features, trailing -- -, no hardcoded --model
  const codex = buildReadonlyAgentArgs({ provider: 'codex', outputFile: '/tmp/out.json' });
  assert.equal(codex.command, 'codex');
  assert.equal(codex.args[0], 'exec');
  assert.equal(codex.args[codex.args.indexOf('--sandbox') + 1], 'read-only');
  assert.ok(codex.args.includes('--ignore-rules'));
  assert.ok(codex.args.includes('web_search="disabled"'));
  assert.ok(codex.args.includes('mcp_servers={}'));
  for (const feat of CODEX_DISABLED_FEATURES) {
    assert.ok(codex.args.includes(`features.${feat}=false`), `missing disabled feature ${feat}`);
  }
  assert.deepEqual(codex.args.slice(-2), ['--', '-']);
  assert.equal(codex.args.includes('--model'), false, 'must not hardcode a default model');

  // 2. claude: -p --permission-mode plan --tools Read,Glob,Grep + optional --json-schema + caller model
  const schema = { type: 'object', required: ['ok'], properties: { ok: { type: 'boolean' } } };
  const claude = buildReadonlyAgentArgs({ provider: 'claude', model: 'caller-chosen-model', jsonSchema: schema });
  assert.equal(claude.command, 'claude');
  assert.ok(claude.args.includes('-p'));
  assert.equal(claude.args[claude.args.indexOf('--permission-mode') + 1], 'plan');
  assert.equal(claude.args[claude.args.indexOf('--tools') + 1], 'Read,Glob,Grep');
  assert.equal(claude.args[claude.args.indexOf('--json-schema') + 1], JSON.stringify(schema));
  assert.equal(claude.args[claude.args.indexOf('--model') + 1], 'caller-chosen-model');

  // 3. gemini: non-interactive read-only plan + sandbox + disabled extensions/mcp
  const gemini = buildReadonlyAgentArgs({ provider: 'gemini', adminPolicy: '/tmp/policy.toml' });
  assert.equal(gemini.command, 'gemini');
  assert.ok(gemini.args.includes('-p'));
  assert.ok(gemini.args.includes('--sandbox'));
  assert.equal(gemini.args[gemini.args.indexOf('--approval-mode') + 1], 'plan');
  assert.equal(gemini.args[gemini.args.indexOf('--extensions') + 1], 'none');
  assert.equal(gemini.args[gemini.args.indexOf('--admin-policy') + 1], '/tmp/policy.toml');
  assert.equal(gemini.args.includes('--model'), false);

  // 4. agy: read-only plan + sandbox + disabled slash commands
  const agy = buildReadonlyAgentArgs({ provider: 'agy' });
  assert.equal(agy.command, 'agy');
  assert.equal(agy.args[agy.args.indexOf('--mode') + 1], 'plan');
  assert.ok(agy.args.includes('--sandbox'));
  assert.ok(agy.args.includes('--disable-slash-commands'));
  assert.equal(agy.args.includes('--model'), false);

  // Invalid provider and leading-dash model names are rejected
  assert.throws(() => buildReadonlyAgentArgs({ provider: 'unknown-cli' }), /Unsupported read-only agent provider/);
  assert.throws(() => buildReadonlyAgentArgs({ provider: 'codex', model: '--injected' }), /Invalid model name/);
});

test('readonly-agent strictly scrubs tokens/session vars, redacts returned outputs, validates JSON schema, and cleans up timed-out process groups', async t => {
  const dirtyEnv = {
    PATH: process.env.PATH,
    HOME: '/tmp/safe-home',
    LANG: 'C.UTF-8',
    GH_TOKEN: 'ghs_secret_1',
    GITHUB_TOKEN: 'ghp_secret_2',
    GH_HOST: 'enterprise.internal',
    GH_ENTERPRISE_TOKEN: 'ghs_ent_3',
    PDD_CLOUD_TOKEN: 'pddg_cloud_secret_123456',
    NPM_TOKEN: 'npm_secret_token',
    AWS_SECRET_ACCESS_KEY: 'aws_secret_val',
    AWS_SESSION_TOKEN: 'aws_sess_val',
    PDD_AUTOPILOT_CONTEXT: 'ctx-1',
    HERDR_SESSION: 'pdd',
    HERDR_CONFIG: '/tmp/herdr',
    CLAUDECODE: '1',
    CLAUDE_CODE_ENTRYPOINT: 'cli',
    CODEX_THREAD_ID: 'thread-99',
    CODEX_SANDBOX_NETWORK_DISABLED: '1',
    BASH_ENV: '/tmp/hook.sh',
    CUSTOM_API_SECRET: 'my_custom_opaque_secret_xyz',
  };
  const clean = scrubReadonlyEnv(dirtyEnv);
  assert.equal(clean.PATH, process.env.PATH);
  assert.equal(clean.HOME, '/tmp/safe-home');
  assert.equal(clean.LANG, 'C.UTF-8');
  for (const stripped of [
    'GH_TOKEN', 'GITHUB_TOKEN', 'GH_HOST', 'GH_ENTERPRISE_TOKEN', 'PDD_CLOUD_TOKEN',
    'NPM_TOKEN', 'AWS_SECRET_ACCESS_KEY', 'AWS_SESSION_TOKEN', 'PDD_AUTOPILOT_CONTEXT',
    'HERDR_SESSION', 'HERDR_CONFIG', 'CLAUDECODE', 'CLAUDE_CODE_ENTRYPOINT',
    'CODEX_THREAD_ID', 'CODEX_SANDBOX_NETWORK_DISABLED', 'BASH_ENV',
  ]) {
    assert.equal(clean[stripped], undefined, `${stripped} must be stripped`);
  }

  // Output redaction + provider envelope unwrapping + JSON schema validation
  const schema = {
    type: 'object',
    required: ['verdict', 'reason'],
    additionalProperties: false,
    properties: {
      verdict: { type: 'string', enum: ['pass', 'fail'] },
      reason: { type: 'string', minLength: 1 },
    },
  };
  const claudeRun = await runReadonlyAgent({
    provider: 'claude',
    prompt: 'check',
    env: dirtyEnv,
    jsonSchema: schema,
  }, {
    run: async (_cmd, _args, opts) => {
      assert.equal(opts.env.GH_TOKEN, undefined);
      assert.equal(opts.env.CLAUDECODE, undefined);
      return {
        code: 0,
        stdout: JSON.stringify({
          result: JSON.stringify({
            verdict: 'pass',
            reason: 'Clean without ghp_secret_2 or my_custom_opaque_secret_xyz',
          }),
        }),
        stderr: 'Bearer topsecretbearer999',
      };
    },
  });
  assert.equal(claudeRun.ok, true);
  assert.equal(claudeRun.parsed.verdict, 'pass');
  assert.ok(!claudeRun.parsed.reason.includes('ghp_secret_2'));
  assert.ok(!claudeRun.parsed.reason.includes('my_custom_opaque_secret_xyz'));
  assert.ok(!claudeRun.stdout.includes('my_custom_opaque_secret_xyz'));
  assert.ok(!claudeRun.stderr.includes('topsecretbearer999'));

  // Schema violation fails closed
  const invalidSchemaRun = await runReadonlyAgent({
    provider: 'gemini',
    prompt: 'check',
    env: dirtyEnv,
    jsonSchema: schema,
  }, {
    run: async () => ({ code: 0, stdout: JSON.stringify({ verdict: 'maybe', reason: 'invalid enum', extra: 1 }), stderr: '' }),
  });
  assert.equal(invalidSchemaRun.ok, false);
  assert.ok(invalidSchemaRun.schemaErrors.length >= 2);
  assert.equal(validateJsonAgainstSchema({ verdict: 'pass', reason: 'ok' }, schema).ok, true);
  assert.equal(extractJsonObject('```json\n{"a":1}\n```')?.a, 1);
  assert.ok(!redactReadonlyOutput('https://user:pw@example.test/?token=abc').includes('pw'));

  // Real subprocess timeout enforces process-group cleanup (grandchild stopped before writing marker)
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-readonly-timeout-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const started = join(scratch, 'started');
  const escaped = join(scratch, 'escaped');
  const hangScript = join(scratch, 'hang.cjs');
  writeFileSync(
    hangScript,
    `const { spawn } = require('node:child_process'); const fs = require('node:fs');
spawn(process.execPath, ['-e', ${JSON.stringify(`require('node:fs').writeFileSync(${JSON.stringify(started)}, '1'); setTimeout(() => require('node:fs').writeFileSync(${JSON.stringify(escaped)}, '1'), 1200);`)}], { stdio: 'ignore' });
setInterval(() => {}, 1000);`,
  );
  const fakeCli = join(scratch, 'fake-cli.sh');
  writeFileSync(fakeCli, `#!/bin/sh\nexec "${process.execPath}" "${hangScript}"\n`, { mode: 0o755 });
  const timedOut = await runReadonlyAgent({
    provider: 'agy',
    command: fakeCli,
    cwd: scratch,
    env: { PATH: process.env.PATH, HOME: scratch },
    timeoutMs: 350,
  });
  assert.equal(timedOut.ok, false);
  assert.match(timedOut.error, /timeout/i);
  await new Promise(r => setTimeout(r, 1400));
  assert.equal(existsSync(started), true, 'grandchild started before timeout');
  assert.equal(existsSync(escaped), false, 'process-group kill stopped grandchild before escape');
});

test('ai-lint.mjs and codex-lint.mjs have ZERO runtime-seam imports, dispatch across all 4 providers, and preserve codex-lint facade', async t => {
  const root = new URL('../..', import.meta.url);
  const readonlySrc = readFileSync(new URL('src/shared/readonly-agent.mjs', root), 'utf8');
  const aiLintSrc = readFileSync(new URL('src/autopilot/ai-lint.mjs', root), 'utf8');
  const facadeSrc = readFileSync(new URL('src/codex-lint.mjs', root), 'utf8');

  const stripComments = src => src.replace(/\/\*[\s\S]*?\*\//g, '').replace(/\/\/[^\n]*/g, '');
  assert.doesNotMatch(stripComments(readonlySrc), /runtime-seam|autopilot\/|core\/|accounts\/|workflow-/);
  assert.doesNotMatch(stripComments(aiLintSrc), /runtime-seam/);
  assert.doesNotMatch(stripComments(facadeSrc), /runtime-seam/);
  assert.ok(facadeSrc.split('\n').length <= 40, 'codex-lint.mjs must stay a <=40L facade');
  assert.equal(buildCodexLintPrompt, buildAiLintPrompt);
  assert.equal(groupCodexLintBatches, groupAiLintBatches);

  const scratch = mkdtempSync(join(tmpdir(), 'pdd-ai-lint-multi-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const repo = join(scratch, 'repo');
  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'user_stories'), { recursive: true });
  writeFileSync(join(repo, 'prompts/calc.prompt.md'), '# Calc\n\nAdd integers.\n\n## Dependencies\n\nNone.\n');
  writeFileSync(join(repo, 'user_stories/calc.md'), '# Calc\n\nAs a shopper, I want totals added, so that I see my bill.\n\n## Acceptance criteria\n\n1. 2 + 3 returns 5.\n');
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=t@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const env = { HOME: scratch, PATH: process.env.PATH, GH_TOKEN: 'ghs_must_scrub' };
  const payload = {
    files: [
      { path: 'prompts/calc.prompt.md', verdict: 'pass', summary: 'Clear contract.', issues: [] },
      { path: 'user_stories/calc.md', verdict: 'pass', summary: 'Clear Story.', issues: [] },
    ],
  };

  for (const provider of READONLY_PROVIDERS) {
    let seenCmd = null, seenArgs = null;
    const out = sink(), err = sink();
    const code = await runAiLint(
      { cwd: repo, words: [], provider, json: true, env },
      {
        stdout: out,
        stderr: err,
        runAgentProcess: async (cmd, args, opts) => {
          seenCmd = cmd; seenArgs = args;
          assert.equal(opts.env.GH_TOKEN, undefined);
          if (provider === 'codex') {
            writeFileSync(args[args.indexOf('--output-last-message') + 1], JSON.stringify(payload));
            return { code: 0, stdout: '', stderr: '' };
          }
          // Non-codex providers return wrapped JSON envelope on stdout
          return { code: 0, stdout: JSON.stringify({ result: JSON.stringify(payload) }), stderr: '' };
        },
      },
    );
    assert.equal(code, 0, `${provider}: ${err.text}`);
    assert.equal(seenCmd, provider);
    if (provider === 'codex') assert.equal(seenArgs[seenArgs.indexOf('--sandbox') + 1], 'read-only');
    if (provider === 'claude') assert.equal(seenArgs[seenArgs.indexOf('--permission-mode') + 1], 'plan');
    if (provider === 'gemini') assert.equal(seenArgs[seenArgs.indexOf('--approval-mode') + 1], 'plan');
    if (provider === 'agy') assert.equal(seenArgs[seenArgs.indexOf('--mode') + 1], 'plan');
    const json = JSON.parse(out.text);
    assert.equal(json.schema_version, 'pdd.codex-lint.v1');
    assert.equal(json.provider, provider);
    assert.equal(json.ok, true);
    assert.equal(json.passed, 2);
  }

  // Unknown provider exits 2 cleanly
  const badErr = sink();
  assert.equal(await runAiLint({ cwd: repo, provider: 'bogus', env }, { stdout: sink(), stderr: badErr }), 2);
  assert.match(badErr.text, /Unsupported --provider/);

  // Facade runCodexLint still defaults to codex and passes
  const facOut = sink(), facErr = sink();
  const facCode = await runCodexLint(
    { cwd: repo, words: [], json: true, env },
    {
      stdout: facOut, stderr: facErr,
      runAgentProcess: async (cmd, args) => {
        assert.equal(cmd, 'codex');
        writeFileSync(args[args.indexOf('--output-last-message') + 1], JSON.stringify(payload));
        return { code: 0, stdout: '', stderr: '' };
      },
    },
  );
  assert.equal(facCode, 0, facErr.text);
  assert.equal(JSON.parse(facOut.text).schema_version, 'pdd.codex-lint.v1');
});
