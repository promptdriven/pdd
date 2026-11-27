import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  CODEX_DISABLED_FEATURES,
  CODEX_TOOL_LOCKOUT_FEATURES,
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

test('readonly-agent builds OS read-only sandbox flags for codex/claude/gemini (dropping standalone agy), zero hardcoded models, configurable Gemini sandbox (#13), and strict provider/model validation (#12)', async () => {
  assert.deepEqual(READONLY_PROVIDERS, ['codex', 'claude', 'gemini']);

  const codex = buildReadonlyAgentArgs({ provider: 'codex', outputFile: '/tmp/out.json' });
  assert.equal(codex.command, 'codex');
  assert.equal(codex.args[0], 'exec');
  assert.equal(codex.args[codex.args.indexOf('--sandbox') + 1], 'read-only');
  assert.ok(codex.args.includes('--ignore-rules'));
  for (const feat of CODEX_DISABLED_FEATURES) assert.ok(codex.args.includes(`features.${feat}=false`));
  assert.deepEqual(CODEX_TOOL_LOCKOUT_FEATURES, ['shell_tool', 'unified_exec', 'code_mode', 'code_mode_host']);
  for (const feat of CODEX_TOOL_LOCKOUT_FEATURES) assert.equal(codex.args.includes(`features.${feat}=false`), false, 'disableTools=false allows read-only sandbox file inspection');
  const codexLocked = buildReadonlyAgentArgs({ provider: 'codex', disableTools: true });
  for (const feat of CODEX_TOOL_LOCKOUT_FEATURES) assert.ok(codexLocked.args.includes(`features.${feat}=false`), 'disableTools=true locks out shell_tool, unified_exec, code_mode, and code_mode_host');
  assert.deepEqual(codex.args.slice(-2), ['--', '-']);
  assert.equal(codex.args.includes('--model'), false);

  const schema = { type: 'object', required: ['ok'], properties: { ok: { type: 'boolean' } } };
  const claude = buildReadonlyAgentArgs({ provider: 'claude', model: 'caller-chosen-model', jsonSchema: schema });
  assert.equal(claude.args[claude.args.indexOf('--permission-mode') + 1], 'plan');
  assert.equal(claude.args[claude.args.indexOf('--tools') + 1], 'Read,Glob,Grep');
  assert.equal(claude.args[claude.args.indexOf('--json-schema') + 1], JSON.stringify(schema));
  assert.equal(claude.args[claude.args.indexOf('--model') + 1], 'caller-chosen-model');

  const claudeNoTools = buildReadonlyAgentArgs({ provider: 'claude', disableTools: true });
  assert.equal(claudeNoTools.args[claudeNoTools.args.indexOf('--tools') + 1], '');

  const gemini = buildReadonlyAgentArgs({ provider: 'gemini', adminPolicy: '/tmp/policy.toml' });
  assert.ok(gemini.args.includes('--sandbox'));
  assert.equal(gemini.args[gemini.args.indexOf('--approval-mode') + 1], 'plan');
  assert.equal(gemini.args[gemini.args.indexOf('--admin-policy') + 1], '/tmp/policy.toml');
  const geminiNoSandbox = buildReadonlyAgentArgs({ provider: 'gemini', sandbox: false });
  assert.equal(geminiNoSandbox.args.includes('--sandbox'), false, 'Gemini --sandbox is configurable (#13)');

  assert.throws(() => buildReadonlyAgentArgs({ provider: 'agy' }), /Unsupported read-only agent provider/);
  assert.throws(() => buildReadonlyAgentArgs({ provider: 'unknown-cli' }), /Unsupported read-only agent provider/);
  assert.throws(() => buildReadonlyAgentArgs({ provider: 'codex', model: '--injected' }), /Invalid model name/);

  // #12: runReadonlyAgent returns structured error reply on invalid provider/model (never throws or leaks temp dirs)
  const badModelRes = await runReadonlyAgent({ provider: 'codex', model: '--bad' });
  assert.equal(badModelRes.ok, false);
  assert.match(badModelRes.error, /Invalid model name/);
  const badProvRes = await runReadonlyAgent({ provider: 'bogus' });
  assert.equal(badProvRes.ok, false);
  assert.match(badProvRes.error, /Unsupported read-only agent provider/);
});

test('readonly-agent scrubs env (#6/#13), preserves raw parsed JSON before redaction (#8), fixes JSON extraction (#11), validates pattern/const/maxLength/anyOf (#23), and cleans up process groups', async t => {
  const dirtyEnv = {
    PATH: process.env.PATH, HOME: '/tmp/safe-home', LANG: 'C.UTF-8',
    GH_TOKEN: 'ghs_secret_1', GITHUB_TOKEN: 'ghp_secret_2', GH_HOST: 'enterprise.internal',
    PDD_CLOUD_TOKEN: 'pddg_cloud_secret_123456', NPM_TOKEN: 'npm_secret_token',
    AWS_SECRET_ACCESS_KEY: 'aws_secret_val', AWS_ACCESS_KEY_ID: 'AKIA123',
    ANTHROPIC_AUTH_TOKEN: 'anth-secret', CODEX_API_KEY: 'codex-secret',
    NODE_AUTH_TOKEN: 'node-secret', HF_TOKEN: 'hf-secret', SSH_AUTH_SOCK: '/tmp/ssh.sock',
    DATABASE_PASSWORD: 'dbpw', SLACK_BOT_TOKEN: 'xoxb-1',
    GEMINI_API_KEY: 'gem-key-123', GOOGLE_API_KEY: 'goog-key-456',
    PDD_AUTOPILOT_CONTEXT: 'ctx-1', HERDR_SESSION: 'pdd', CLAUDECODE: '1',
    CODEX_THREAD_ID: 'thread-99', BASH_ENV: '/tmp/hook.sh',
    MY_TOKEN: 'fail', TOKENIZERS_PARALLELISM: 'false',
    CUSTOM_API_SECRET: 'my_custom_opaque_secret_xyz',
  };

  const codexEnv = scrubReadonlyEnv(dirtyEnv, { provider: 'codex' });
  assert.equal(codexEnv.GEMINI_API_KEY, undefined, 'GEMINI_API_KEY stripped for non-gemini');
  assert.equal(codexEnv.ANTHROPIC_AUTH_TOKEN, undefined);
  assert.equal(codexEnv.SSH_AUTH_SOCK, undefined);
  const geminiEnv = scrubReadonlyEnv(dirtyEnv, { provider: 'gemini' });
  assert.equal(geminiEnv.GEMINI_API_KEY, 'gem-key-123', 'GEMINI_API_KEY preserved for gemini (#13)');
  assert.equal(geminiEnv.GOOGLE_API_KEY, 'goog-key-456', 'GOOGLE_API_KEY preserved for gemini (#13)');
  assert.equal(geminiEnv.GH_TOKEN, undefined);

  // #11: extractJsonObject without accept does NOT clobber real top-level { result: {...}, ok: true }; WITH accept tries ALL candidates!
  const realOuter = extractJsonObject(JSON.stringify({ result: { nested: 1 }, status: 'ok' }));
  assert.deepEqual(realOuter, { result: { nested: 1 }, status: 'ok' });
  const multiCand = 'Example: ```json\n{"note":"ignore"}\n```\nActual: {"files":[{"path":"a.md"}]}';
  const picked = extractJsonObject(multiCand, { accept: doc => Array.isArray(doc?.files) });
  assert.deepEqual(picked, { files: [{ path: 'a.md' }] });

  // #23: Schema validation supports const, pattern, maxLength, anyOf
  const richSchema = {
    type: 'object',
    required: ['version', 'verdict', 'code', 'tag'],
    additionalProperties: false,
    properties: {
      version: { const: 1 },
      verdict: { enum: ['pass', 'fail'] },
      code: { type: 'string', pattern: '^[a-z-]+$', maxLength: 10 },
      tag: { anyOf: [{ type: 'string', minLength: 1 }, { type: 'null' }] },
    },
  };
  assert.equal(validateJsonAgainstSchema({ version: 1, verdict: 'fail', code: 'ok-rule', tag: null }, richSchema).ok, true);
  assert.equal(validateJsonAgainstSchema({ version: 2, verdict: 'fail', code: 'ok-rule', tag: null }, richSchema).ok, false);
  assert.equal(validateJsonAgainstSchema({ version: 1, verdict: 'fail', code: 'BAD_CASE', tag: null }, richSchema).ok, false);
  assert.equal(validateJsonAgainstSchema({ version: 1, verdict: 'fail', code: 'too-long-code', tag: null }, richSchema).ok, false);
  assert.equal(validateJsonAgainstSchema({ version: 1, verdict: 'fail', code: 'ok', tag: 42 }, richSchema).ok, false);

  // #8: Ambient MY_TOKEN=fail MUST NOT corrupt parsed verdict before schema validation; stdout/stderr ARE still redacted!
  const claudeRun = await runReadonlyAgent({
    provider: 'claude', prompt: 'check', env: dirtyEnv, jsonSchema: richSchema,
  }, {
    run: async (_cmd, _args, opts) => {
      assert.equal(opts.env.GH_TOKEN, undefined);
      assert.equal(opts.env.CLAUDECODE, undefined);
      return {
        code: 0,
        stdout: JSON.stringify({ result: JSON.stringify({ version: 1, verdict: 'fail', code: 'ok-rule', tag: 'x' }) }),
        stderr: 'Bearer topsecretbearer999 my_custom_opaque_secret_xyz',
      };
    },
  });
  assert.equal(claudeRun.ok, true, `MY_TOKEN=fail must not corrupt schema validation (#8): ${claudeRun.error}`);
  assert.equal(claudeRun.parsed.verdict, 'fail');
  assert.ok(!claudeRun.stderr.includes('topsecretbearer999'));
  assert.ok(!claudeRun.stderr.includes('my_custom_opaque_secret_xyz'));
  assert.ok(!redactReadonlyOutput('https://user:pw@example.test/?token=abc').includes('pw'));

  // Real subprocess timeout enforces process-group cleanup
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-readonly-timeout-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const started = join(scratch, 'started'), escaped = join(scratch, 'escaped'), hangScript = join(scratch, 'hang.cjs');
  writeFileSync(
    hangScript,
    `const { spawn } = require('node:child_process');
spawn(process.execPath, ['-e', ${JSON.stringify(`require('node:fs').writeFileSync(${JSON.stringify(started)}, '1'); setTimeout(() => require('node:fs').writeFileSync(${JSON.stringify(escaped)}, '1'), 1200);`)}], { stdio: 'ignore' });
setInterval(() => {}, 1000);`,
  );
  const fakeCli = join(scratch, 'fake-cli.sh');
  writeFileSync(fakeCli, `#!/bin/sh\nexec "${process.execPath}" "${hangScript}"\n`, { mode: 0o755 });
  const timedOut = await runReadonlyAgent({ provider: 'claude', command: fakeCli, cwd: scratch, env: { PATH: process.env.PATH, HOME: scratch }, timeoutMs: 350 });
  assert.equal(timedOut.ok, false);
  assert.match(timedOut.error, /timeout/i);
  await new Promise(r => setTimeout(r, 1400));
  assert.equal(existsSync(started), true);
  assert.equal(existsSync(escaped), false);
});

test('ai-lint.mjs has ZERO runtime-seam imports, enforces disableTools/deny-all sandbox (#7), preserves raw verdicts/paths under MY_TOKEN=fail & TOKENIZERS_PARALLELISM=false (#8), full rubric (#10), dynamic rerun hint (#22), and codex-lint facade', async t => {
  const root = new URL('../..', import.meta.url);
  const readonlySrc = readFileSync(new URL('src/shared/readonly-agent.mjs', root), 'utf8');
  const aiLintSrc = readFileSync(new URL('src/autopilot/ai-lint.mjs', root), 'utf8');
  const facadeSrc = readFileSync(new URL('src/codex-lint.mjs', root), 'utf8');
  const stripComments = src => src.replace(/\/\*[\s\S]*?\*\//g, '').replace(/\/\/[^\n]*/g, '');

  assert.doesNotMatch(stripComments(readonlySrc), /runtime-seam|autopilot\/|core\/|accounts\/|workflow-/);
  assert.doesNotMatch(stripComments(aiLintSrc), /runtime-seam/);
  assert.doesNotMatch(stripComments(facadeSrc), /runtime-seam/);
  assert.match(facadeSrc, /(?:Generated from|Prompt:) prompts\/cli\/codex-lint\.prompt\.md/);
  assert.ok(facadeSrc.split('\n').length <= 40);
  assert.equal(buildCodexLintPrompt, buildAiLintPrompt);
  assert.equal(groupCodexLintBatches, groupAiLintBatches);

  // #10: Verify full grading rubric phrases are intact in buildAiLintPrompt
  const fullRubric = buildAiLintPrompt(
    [{ path: 'prompts/a.prompt.md', kind: 'prompt', text: '# A' }, { path: 'user_stories/a.md', kind: 'story', text: '# A' }],
    { pairs: [{ story: 'user_stories/a.md', prompts: ['prompts/a.prompt.md'] }] },
  );
  assert.match(fullRubric, /## Domain decisions/);
  assert.match(fullRubric, /conflicting defaults or error behavior/);
  assert.match(fullRubric, /silent scope drift/);
  assert.match(fullRubric, /works cleanly/);

  const scratch = mkdtempSync(join(tmpdir(), 'pdd-ai-lint-multi-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const repo = join(scratch, 'repo');
  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'user_stories'), { recursive: true });
  writeFileSync(join(repo, 'prompts/false-positive.prompt.md'), '# False Positive\n\nHandle edge cases.\n\n## Dependencies\n\nNone.\n');
  writeFileSync(join(repo, 'user_stories/calc.md'), '# Calc\n\nAs a shopper, I want totals added, so that I see my bill.\n\n## Acceptance criteria\n\n1. 2 + 3 returns 5.\n');
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=t@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  // #8: Ambient MY_TOKEN=fail and TOKENIZERS_PARALLELISM=false MUST NOT turn fail -> pass or corrupt path containing "false"!
  const env = { HOME: scratch, PATH: process.env.PATH, GH_TOKEN: 'ghs_must_scrub', MY_TOKEN: 'fail', TOKENIZERS_PARALLELISM: 'false', REAL_SECRET_KEY: 'super_secret_val_999' };
  const failingPayload = {
    files: [
      { path: 'prompts/false-positive.prompt.md', verdict: 'fail', summary: 'Needs clearer contract (saw super_secret_val_999).', issues: [{ line: 3, rule: 'prompt-readability', message: 'Avoid super_secret_val_999.' }] },
      { path: 'user_stories/calc.md', verdict: 'pass', summary: 'Clear Story.', issues: [] },
    ],
  };

  for (const provider of READONLY_PROVIDERS) {
    let seenCmd = null, seenArgs = null, seenCwd = null, policyContents = null;
    const out = sink(), err = sink();
    const code = await runAiLint(
      { cwd: repo, words: [], provider, json: true, env },
      {
        stdout: out, stderr: err,
        runAgentProcess: async (cmd, args, opts) => {
          seenCmd = cmd; seenArgs = args; seenCwd = opts.cwd;
          assert.equal(opts.env.GH_TOKEN, undefined);
          if (provider === 'gemini') {
            const pFile = args[args.indexOf('--admin-policy') + 1];
            policyContents = readFileSync(pFile, 'utf8');
          }
          if (provider === 'codex') {
            writeFileSync(args[args.indexOf('--output-last-message') + 1], JSON.stringify(failingPayload));
            return { code: 0, stdout: '', stderr: '' };
          }
          return { code: 0, stdout: JSON.stringify({ result: JSON.stringify(failingPayload) }), stderr: '' };
        },
      },
    );
    assert.equal(code, 1, `${provider}: failing verdict must STAY exit 1 under MY_TOKEN=fail (#8): ${err.text}`);
    assert.equal(seenCmd, provider);
    // #7: Isolated empty cwd + provider tool lockouts
    assert.notEqual(seenCwd, repo, `${provider}: must run in isolated empty temp cwd, not repo root (#7)`);
    if (provider === 'claude') assert.equal(seenArgs[seenArgs.indexOf('--tools') + 1], '', 'Claude ai-lint must disable tools (#7)');
    if (provider === 'gemini') assert.match(policyContents ?? '', /decision = "deny"/, 'Gemini ai-lint must attach deny-all admin policy (#7)');
    const json = JSON.parse(out.text);
    assert.equal(json.schema_version, 'pdd.codex-lint.v1');
    assert.equal(json.provider, provider);
    assert.equal(json.failed, 1);
    assert.equal(json.files[0].path, 'prompts/false-positive.prompt.md');
    assert.equal(json.files[0].status, 'fail');
    assert.ok(!out.text.includes('super_secret_val_999'), 'prose summary/message must still redact real secrets');
  }

  // #22: Unreadable response for non-codex provider shows dynamic provider hint (not pdd lint --codex)
  const badReplyErr = sink();
  const badReplyCode = await runAiLint(
    { cwd: repo, words: [], provider: 'claude', env },
    { stdout: sink(), stderr: badReplyErr, runAgentProcess: async () => ({ code: 0, stdout: 'not json', stderr: '' }) },
  );
  assert.equal(badReplyCode, 1);
  assert.match(badReplyErr.text, /Claude lint.*--provider claude/);
  assert.doesNotMatch(badReplyErr.text, /pdd lint --codex/);

  // Facade runCodexLint still works cleanly
  const facOut = sink(), facErr = sink();
  const facCode = await runCodexLint(
    { cwd: repo, words: [], json: true, env: { HOME: scratch, PATH: process.env.PATH } },
    {
      stdout: facOut, stderr: facErr,
      runAgentProcess: async (cmd, args) => {
        assert.equal(cmd, 'codex');
        writeFileSync(args[args.indexOf('--output-last-message') + 1], JSON.stringify({
          files: [
            { path: 'prompts/false-positive.prompt.md', verdict: 'pass', summary: 'Ok.', issues: [] },
            { path: 'user_stories/calc.md', verdict: 'pass', summary: 'Ok.', issues: [] },
          ],
        }));
        return { code: 0, stdout: '', stderr: '' };
      },
    },
  );
  assert.equal(facCode, 0, facErr.text);
  assert.equal(JSON.parse(facOut.text).schema_version, 'pdd.codex-lint.v1');
});
