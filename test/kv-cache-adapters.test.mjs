import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { askAgent } from '../src/agent-adapters.mjs';
import { buildAgentInput } from '../src/agent-packet.mjs';
import { chatCommand, chatLaunch } from '../src/workflow-chat.mjs';
import { openRun, startRun } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const entries = [
  {
    entry: 'prompts/orders.prompt.md#place_order',
    prompt_path: 'prompts/orders.prompt.md',
    operation: 'place_order',
    http: { method: 'POST', path: '/api/orders' },
    input_schema: {
      type: 'object',
      properties: { item: { type: 'string' }, qty: { type: 'integer' } },
      required: ['item', 'qty'],
      additionalProperties: false,
    },
  },
];

const validReply = {
  say: 'Try placing an order first.',
  fill: { entry: entries[0].entry, input: { item: 'book', qty: 2 } },
  apply: true,
};

const CLAUDE_21_HELP = `Usage: claude [options] [command] [prompt]
Options:
  --bare  Explicitly provide context via: --system-prompt[-file], --append-system-prompt[-file]
  --exclude-dynamic-system-prompt-sections  Move per-machine sections from the system prompt into the first user message.
  --no-chrome
  --no-session-persistence
  --output-format <format>
  --permission-mode <mode>
  --permission-prompts <target>
  --safe-mode
  --strict-mcp-config
  --system-prompt <prompt>
  --system-prompt-snapshot <on|off>
  --tools <tools...>
`;

test('Claude splits static Try prefix into --system-prompt-file, sends only dynamic turn JSON on stdin, cleans temp files, and stays byte-identical across turns', async t => {
  const rules = [{ path: 'prompts/orders.prompt.md', text: '# Orders\n\n' + 'Static rule line.\n'.repeat(250), summary: '# Orders', truncated: false }];
  const card = (nextStep, saved) =>
    `You are the Try guide.\nOpened Story: orders.\nNext step: ${nextStep}.\nSave target: tests/orders.json (exists, 2 steps, ${saved} saved cases from this Try).`;

  const turnContexts = [
    {
      project: card('Finish the Try', 0),
      coverage: { text: 'Coverage: 0/2 criteria pass · 0/1 surfaces tried' },
      productRules: rules,
      criteria: [{ id: 'AC1', knownid: 'orders#AC1', story_path: 'user_stories/orders.md', text: 'Place order', state: 'todo', entry: entries[0].entry, input: { qty: 2, item: 'book' } }],
      progress: { line: 'Story progress: 0 of 1 pass', items: [{ id: 'AC1', state: 'todo' }] },
      world: { orders: [] },
      runs: [],
      fields: { entry: entries[0].entry, input: { item: '', qty: 1 }, preloaded: true },
      mode: 'chat',
      conversation: [],
      message: 'What should I try first?',
      changed: false,
    },
    {
      project: 'Local copy changed: checks use your current local Story/test copy.\n' + card('pdd test orders', 1),
      coverage: { text: 'Coverage: 1/2 criteria pass · 1/1 surfaces tried' },
      productRules: rules,
      criteria: [{ id: 'AC1', knownid: 'orders#AC1', story_path: 'user_stories/orders.md', text: 'Place order', state: 'pass', entry: entries[0].entry, input: { item: 'book', qty: 2 } }],
      progress: { line: 'Story progress: 1 of 1 pass', items: [{ id: 'AC1', state: 'pass', check_passed: true }] },
      world: { orders: [{ id: 1, item: 'book', qty: 2 }] },
      runs: [{ id: 'r1', entry: entries[0].entry, input: { item: 'book', qty: 2 }, result: { status: 201 } }],
      fields: { entry: entries[0].entry, input: { item: 'book', qty: 2 }, preloaded: false },
      mode: 'walk',
      conversation: [{ person: 'What should I try first?', say: 'Try placing an order first.', apply: true }],
      message: 'What happened on that run?',
      changed: true,
    },
    {
      project: card('pdd approve prompts/orders.prompt.md', 2),
      coverage: { text: 'Coverage: 2/2 criteria pass · 1/1 surfaces tried' },
      productRules: rules,
      criteria: [{ id: 'AC1', knownid: 'orders#AC1', story_path: 'user_stories/orders.md', text: 'Place order', state: 'pass', entry: entries[0].entry, input: { item: 'book', qty: 2 } }],
      progress: { line: 'Story progress: 1 of 1 pass', items: [{ id: 'AC1', state: 'pass', check_passed: true }] },
      world: { orders: [{ id: 1, item: 'book', qty: 2 }, { id: 2, item: 'pen', qty: 5 }] },
      runs: [
        { id: 'r1', entry: entries[0].entry, input: { item: 'book', qty: 2 }, result: { status: 201 } },
        { id: 'r2', entry: entries[0].entry, input: { item: 'pen', qty: 5 }, result: { status: 201 } },
      ],
      fields: { entry: entries[0].entry, input: { item: 'pen', qty: 5 }, preloaded: false },
      mode: 'chat',
      conversation: [
        { person: 'What should I try first?', say: 'Try placing an order first.', apply: true },
        { person: 'What happened on that run?', say: 'AC1 passed with status 201.', apply: false },
      ],
      message: 'Can we save our own case?',
      changed: false,
    },
  ];

  const capturedTurns = [];
  for (const ctx of turnContexts) {
    let promptFilePath;
    const got = await askAgent({
      agent: 'claude',
      entries,
      supportsApply: true,
      supportsRun: true,
      env: { API_SECRET: 'top-secret-cred' },
      context: { ...ctx, secretToken: 'hidden-field-secret', message: `${ctx.message} top-secret-cred` },
      run: async (cmd, args, opts) => {
        if (args.includes('--help')) return { code: 0, stdout: CLAUDE_21_HELP, stderr: '' };
        const fileIdx = args.indexOf('--system-prompt-file');
        assert.ok(fileIdx !== -1, 'expected --system-prompt-file');
        assert.ok(args.includes('--exclude-dynamic-system-prompt-sections'));
        assert.ok(args.includes('--no-session-persistence'));
        promptFilePath = args[fileIdx + 1];
        assert.equal(fs.statSync(promptFilePath).mode & 0o777, 0o600);
        const systemPrompt = fs.readFileSync(promptFilePath, 'utf8');
        capturedTurns.push({ args: [...args], systemPrompt, stdin: opts.input });
        return { code: 0, stdout: JSON.stringify({ type: 'result', is_error: false, result: JSON.stringify(validReply) }), stderr: '' };
      },
    });
    assert.deepEqual(got, validReply);
    assert.equal(fs.existsSync(promptFilePath), false, 'temporary system prompt file must be removed after completion');
  }

  assert.equal(capturedTurns.length, 3);
  assert.ok(Buffer.byteLength(capturedTurns[0].systemPrompt, 'utf8') > 4500);
  // Static system prompt is 100% byte-identical across Turn 1 -> Turn 2 -> Turn 3.
  assert.equal(capturedTurns[1].systemPrompt, capturedTurns[0].systemPrompt);
  assert.equal(capturedTurns[2].systemPrompt, capturedTurns[0].systemPrompt);

  for (let i = 0; i < capturedTurns.length; i++) {
    const { systemPrompt, stdin } = capturedTurns[i];
    assert.ok(Buffer.byteLength(systemPrompt, 'utf8') + Buffer.byteLength(stdin, 'utf8') <= 24576);
    assert.ok(!systemPrompt.includes('top-secret-cred') && !stdin.includes('top-secret-cred'));
    assert.ok(!systemPrompt.includes('hidden-field-secret') && !stdin.includes('hidden-field-secret'));
    const staticJson = JSON.parse(systemPrompt.slice(systemPrompt.indexOf('\nDATA\n') + 6));
    assert.deepEqual(Object.keys(staticJson), ['productRules', 'ways', 'project', 'criteria']);
    const turnJson = JSON.parse(stdin);
    assert.deepEqual(Object.keys(turnJson), ['conversation', 'coverage', 'progress', 'try', 'message', 'changed']);
    assert.equal(turnJson.conversation.length, i);
  }

  // Verify cleanup also happens when the model subprocess throws and under tight 24,576-byte compaction.
  let thrownFilePath;
  const failed = await askAgent({
    agent: 'claude',
    entries,
    context: {
      message: 'compact near cap',
      fields: { entry: entries[0].entry, input: { item: 'x'.repeat(16000), qty: 1 } },
      world: 'w'.repeat(800),
      conversation: Array.from({ length: 6 }, () => ({ person: 'p'.repeat(500), say: 's'.repeat(500) })),
    },
    run: async (cmd, args, opts) => {
      if (args.includes('--help')) return { code: 0, stdout: '--safe-mode --tools --permission-prompts --system-prompt-file <path>', stderr: '' };
      thrownFilePath = args[args.indexOf('--system-prompt-file') + 1];
      const sysBytes = Buffer.byteLength(fs.readFileSync(thrownFilePath, 'utf8'), 'utf8');
      const stdinBytes = Buffer.byteLength(opts.input, 'utf8');
      assert.ok(sysBytes + stdinBytes <= 24576, `split budget ${sysBytes + stdinBytes} must stay <= 24576`);
      throw new Error('simulated subprocess failure');
    },
  });
  assert.equal(failed.error.state, 'error');
  assert.equal(fs.existsSync(thrownFilePath), false, 'temporary system prompt file must be removed on error');
});

test('Claude uses --system-prompt when -file is absent and falls back to full stdin on older CLI builds', async () => {
  // 1. Only --system-prompt advertised -> inline --system-prompt + dynamic stdin
  let inlineCall;
  const gotInline = await askAgent({
    agent: 'claude',
    entries,
    context: { message: 'Explain orders', project: 'Orders Try' },
    run: async (cmd, args, opts) => {
      if (args.includes('--help')) return { code: 0, stdout: '  --safe-mode\n  --tools <t>\n  --permission-prompts <p>\n  --system-prompt <prompt>\n', stderr: '' };
      inlineCall = { args, input: opts.input };
      return { code: 0, stdout: JSON.stringify(validReply), stderr: '' };
    },
  });
  assert.deepEqual(gotInline, validReply);
  assert.ok(inlineCall.args.includes('--system-prompt'));
  assert.ok(!inlineCall.args.includes('--system-prompt-file'));
  assert.ok(!inlineCall.args.includes('--exclude-dynamic-system-prompt-sections'));
  const sysText = inlineCall.args[inlineCall.args.indexOf('--system-prompt') + 1];
  assert.match(sysText, /^Where you are\n/);
  assert.equal(JSON.parse(inlineCall.input).message, 'Explain orders');

  // 2. Older CLI build (even if --system-prompt-snapshot exists without --system-prompt) -> full-stdin fallback
  let legacyCall;
  const expectedFull = buildAgentInput({ context: { message: 'Legacy turn', project: 'Orders Try' }, entries });
  const gotLegacy = await askAgent({
    agent: 'claude',
    entries,
    context: { message: 'Legacy turn', project: 'Orders Try' },
    run: async (cmd, args, opts) => {
      if (args.includes('--help')) return { code: 0, stdout: '  --safe-mode\n  --tools <t>\n  --permission-prompts <p>\n  --system-prompt-snapshot <on|off>\n', stderr: '' };
      legacyCall = { args, input: opts.input };
      return { code: 0, stdout: JSON.stringify(validReply), stderr: '' };
    },
  });
  assert.deepEqual(gotLegacy, validReply);
  assert.ok(!legacyCall.args.includes('--system-prompt'));
  assert.ok(!legacyCall.args.includes('--system-prompt-file'));
  assert.equal(legacyCall.input, expectedFull);
});

test('Gemini --allowed-mcp-server-names uses a deterministic sentinel across turns and avoids collisions with configured MCP servers', async t => {
  const dir = fs.mkdtempSync(join(tmpdir(), 'pdd-gemini-sentinel-'));
  t.after(() => fs.rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'home'), cwd = join(dir, 'repo'), sysSettings = join(dir, 'system-settings.json');
  fs.mkdirSync(join(home, '.gemini'), { recursive: true });
  fs.mkdirSync(join(cwd, '.gemini'), { recursive: true });
  fs.writeFileSync(sysSettings, JSON.stringify({ mcpServers: { github: { command: 'gh-mcp' } } }));
  fs.writeFileSync(join(home, '.gemini', 'settings.json'), JSON.stringify({ mcpServers: { pdd: { command: 'pdd' } } }));

  const geminiHelp = '--approval-mode --admin-policy --extensions --allowed-mcp-server-names --output-format';
  const seenSentinels = [];
  for (const msg of ['Turn 1', 'Turn 2', 'Turn 3']) {
    const res = await askAgent({
      agent: 'gemini',
      cwd,
      entries,
      env: { HOME: home, GEMINI_CLI_SYSTEM_SETTINGS_PATH: sysSettings },
      context: { message: msg },
      run: async (cmd, args) => {
        if (args.includes('--help')) return { code: 0, stdout: geminiHelp, stderr: '' };
        seenSentinels.push(args[args.indexOf('--allowed-mcp-server-names') + 1]);
        return { code: 0, stdout: JSON.stringify({ response: JSON.stringify(validReply) }), stderr: '' };
      },
    });
    assert.deepEqual(res, validReply);
  }
  assert.deepEqual(seenSentinels, ['pdd-disabled-none', 'pdd-disabled-none', 'pdd-disabled-none']);

  // Now configure an MCP server literally named "pdd-disabled-none" in workspace .gemini/settings.json!
  fs.writeFileSync(join(cwd, '.gemini', 'settings.json'), JSON.stringify({ mcpServers: { 'pdd-disabled-none': { command: 'collide' }, other: { command: 'x' } } }));
  const collisionSentinels = [];
  for (const msg of ['Turn A', 'Turn B']) {
    await askAgent({
      agent: 'gemini',
      cwd,
      entries,
      env: { HOME: home, GEMINI_CLI_SYSTEM_SETTINGS_PATH: sysSettings },
      context: { message: msg },
      run: async (cmd, args) => {
        if (args.includes('--help')) return { code: 0, stdout: geminiHelp, stderr: '' };
        collisionSentinels.push(args[args.indexOf('--allowed-mcp-server-names') + 1]);
        return { code: 0, stdout: JSON.stringify({ response: JSON.stringify(validReply) }), stderr: '' };
      },
    });
  }
  assert.equal(collisionSentinels[0], collisionSentinels[1], 'fallback sentinel must still be deterministic across turns');
  assert.notEqual(collisionSentinels[0], 'pdd-disabled-none');
  assert.ok(!['github', 'pdd', 'pdd-disabled-none', 'other'].includes(collisionSentinels[0]));
  assert.match(collisionSentinels[0], /^pdd-disabled-[0-9a-f]{16}$/);
});

test('workflow-chat capability-gates --exclude-dynamic-system-prompt-sections for Claude launch and resume', async t => {
  const sessionId = '11111111-1111-4111-8111-111111111111';
  const withFlag = chatCommand({ agent: 'claude', cwd: '/work', messageFile: '/work/start.md', sessionId, excludeDynamicSystemPromptSections: true });
  assert.match(withFlag, /claude --dangerously-skip-permissions --exclude-dynamic-system-prompt-sections --session-id 11111111-1111-4111-8111-111111111111 /);
  const resumeWithFlag = chatCommand({ agent: 'claude', cwd: '/work', resumeId: sessionId, excludeDynamicSystemPromptSections: true });
  assert.match(resumeWithFlag, /claude --dangerously-skip-permissions --exclude-dynamic-system-prompt-sections --resume '11111111-1111-4111-8111-111111111111'$/);
  const withoutFlag = chatCommand({ agent: 'claude', cwd: '/work', messageFile: '/work/start.md', sessionId });
  assert.doesNotMatch(withoutFlag, /--exclude-dynamic-system-prompt-sections/);

  // End-to-end startRun + openRun (resume) with fake claude executable on PATH advertising vs omitting the flag
  for (const supported of [true, false]) {
    const f = await fixture(t, { agent: 'claude' });
    const bin = join(f.base, 'bin');
    fs.mkdirSync(bin);
    const helpOut = supported ? 'Options:\n  --dangerously-skip-permissions\n  --exclude-dynamic-system-prompt-sections\n' : 'Options:\n  --dangerously-skip-permissions\n';
    fs.writeFileSync(
      join(bin, 'claude'),
      `#!${process.execPath}\nif(process.argv.includes('--help')){process.stdout.write(${JSON.stringify(helpOut)});process.exit(0);}\nprocess.stdout.write(JSON.stringify(process.argv.slice(2)));\n`,
      { mode: 0o755 },
    );
    f.ports.env = { ...f.ports.env, PATH: `${bin}:/usr/bin:/bin` };
    const started = await f.run();
    assert.equal(started.exitCode, 0, started.message);
    const chat = f.record().chats[0];
    const pane = f.herdr.paneOf(chat);
    if (supported) {
      assert.match(pane.commands[0], /claude --dangerously-skip-permissions --exclude-dynamic-system-prompt-sections --session-id /);
      const argv = JSON.parse(execFileSync('/bin/sh', ['-c', pane.commands[0]], { cwd: f.base, env: f.ports.env, encoding: 'utf8' }));
      assert.deepEqual(argv.slice(0, 3), ['--dangerously-skip-permissions', '--exclude-dynamic-system-prompt-sections', '--session-id']);
    } else {
      assert.doesNotMatch(pane.commands[0], /--exclude-dynamic-system-prompt-sections/);
    }

    // Simulate ended chat and verify resume command capability-gates identically
    pane.agent = null;
    const resumed = await openRun({ ref: '17', cwd: f.source }, { ...f.ports, env: { ...f.ports.env, HERDR_ENV: '1' } });
    assert.equal(resumed.exitCode, 0, resumed.message);
    if (supported) {
      assert.match(pane.commands[1], /claude --dangerously-skip-permissions --exclude-dynamic-system-prompt-sections --resume '/);
    } else {
      assert.doesNotMatch(pane.commands[1], /--exclude-dynamic-system-prompt-sections/);
    }
  }
});

test('Gemini MCP sentinel parses JSONC comments/trailing commas, follows symlinks, inspects omitted cwd, and fails closed on unreadable or corrupt settings', async t => {
  const dir = fs.mkdtempSync(join(tmpdir(), 'pdd-gemini-jsonc-'));
  t.after(() => fs.rmSync(dir, { recursive: true, force: true }));
  const geminiHelp = '--approval-mode --admin-policy --extensions --allowed-mcp-server-names --output-format';
  const sysSettings = join(dir, 'system-settings.json');
  fs.writeFileSync(sysSettings, '{\n  // system comment\n  "mcpServers": { "sys": { "url": "http://localhost:8080/*not-comment*/ //keep", }, },\n}\n');

  async function pickSentinel(opts) {
    let sentinel;
    const res = await askAgent({
      agent: 'gemini',
      entries,
      context: { message: 'Check sentinel' },
      ...opts,
      run: async (_cmd, args) => {
        if (args.includes('--help')) return { code: 0, stdout: geminiHelp, stderr: '' };
        sentinel = args[args.indexOf('--allowed-mcp-server-names') + 1];
        return { code: 0, stdout: JSON.stringify({ response: JSON.stringify(validReply) }), stderr: '' };
      },
    });
    assert.deepEqual(res, validReply);
    return sentinel;
  }

  // 1. JSONC line/block comments + trailing commas + Stow/Nix symlinked ~/.gemini/settings.json
  const stowTarget = join(dir, 'dotfiles-gemini-settings.json');
  fs.writeFileSync(
    stowTarget,
    `{
      // Line comment before mcpServers
      /* Block comment with "pdd-disabled-fake" inside comment */
      "mcpServers": {
        "pdd-disabled-none": {
          "command": "node", // inline comment
          "args": ["server.js",],
        },
      },
    }`,
  );
  const stowHome = join(dir, 'stow-home'), cleanCwd = join(dir, 'clean-cwd');
  fs.mkdirSync(join(stowHome, '.gemini'), { recursive: true });
  fs.mkdirSync(cleanCwd, { recursive: true });
  fs.symlinkSync(stowTarget, join(stowHome, '.gemini', 'settings.json'));

  const s1 = await pickSentinel({ cwd: cleanCwd, env: { HOME: stowHome, GEMINI_CLI_SYSTEM_SETTINGS_PATH: sysSettings } });
  const s2 = await pickSentinel({ cwd: cleanCwd, env: { HOME: stowHome, GEMINI_CLI_SYSTEM_SETTINGS_PATH: sysSettings } });
  assert.equal(s1, s2);
  assert.match(s1, /^pdd-disabled-[0-9a-f]{16}$/);

  // 2. Omitted cwd still inspects <process.cwd()>/.gemini/settings.json
  const cleanHome = join(dir, 'clean-home'), omittedWorkspace = join(dir, 'omitted-cwd');
  fs.mkdirSync(join(cleanHome, '.gemini'), { recursive: true });
  fs.mkdirSync(join(omittedWorkspace, '.gemini'), { recursive: true });
  fs.writeFileSync(join(omittedWorkspace, '.gemini', 'settings.json'), '{"mcpServers":{"pdd-disabled-none":{"command":"local"}}}');
  const prevCwd = process.cwd();
  try {
    process.chdir(omittedWorkspace);
    const omittedSentinel = await pickSentinel({ env: { HOME: cleanHome, GEMINI_CLI_SYSTEM_SETTINGS_PATH: sysSettings } });
    assert.match(omittedSentinel, /^pdd-disabled-[0-9a-f]{16}$/);
    assert.notEqual(omittedSentinel, 'pdd-disabled-none');
  } finally {
    process.chdir(prevCwd);
  }

  // 3. Corrupt / unparseable settings.json fails closed to a deterministic hash that cannot match 'pdd-disabled-none' or raw tokens
  const corruptCwd = join(dir, 'corrupt-cwd');
  fs.mkdirSync(join(corruptCwd, '.gemini'), { recursive: true });
  const rawCorrupt = '{"mcpServers": { "pdd-disabled-none": true, "pdd-disabled-deadbeef01234567": true, BROKEN_JSON';
  fs.writeFileSync(join(corruptCwd, '.gemini', 'settings.json'), rawCorrupt);
  const c1 = await pickSentinel({ cwd: corruptCwd, env: { HOME: cleanHome, GEMINI_CLI_SYSTEM_SETTINGS_PATH: sysSettings } });
  const c2 = await pickSentinel({ cwd: corruptCwd, env: { HOME: cleanHome, GEMINI_CLI_SYSTEM_SETTINGS_PATH: sysSettings } });
  assert.equal(c1, c2);
  assert.match(c1, /^pdd-disabled-[0-9a-f]{16}$/);
  assert.ok(!rawCorrupt.includes(c1), 'sentinel must not equal any token in raw corrupt file');

  // 4. Unreadable / broken-symlink settings.json also fails closed deterministically
  const brokenCwd = join(dir, 'broken-cwd');
  fs.mkdirSync(join(brokenCwd, '.gemini'), { recursive: true });
  fs.symlinkSync(join(dir, 'missing-target.json'), join(brokenCwd, '.gemini', 'settings.json'));
  const b1 = await pickSentinel({ cwd: brokenCwd, env: { HOME: cleanHome, GEMINI_CLI_SYSTEM_SETTINGS_PATH: sysSettings } });
  const b2 = await pickSentinel({ cwd: brokenCwd, env: { HOME: cleanHome, GEMINI_CLI_SYSTEM_SETTINGS_PATH: sysSettings } });
  assert.equal(b1, b2);
  assert.match(b1, /^pdd-disabled-[0-9a-f]{16}$/);

  if (process.geteuid?.() !== 0) {
    const chmodCwd = join(dir, 'chmod-cwd');
    fs.mkdirSync(join(chmodCwd, '.gemini'), { recursive: true });
    const unreadable = join(chmodCwd, '.gemini', 'settings.json');
    fs.writeFileSync(unreadable, '{"mcpServers":{"pdd-disabled-none":{"command":"x"}}}', { mode: 0o000 });
    t.after(() => { try { fs.chmodSync(unreadable, 0o600); } catch {} });
    const u1 = await pickSentinel({ cwd: chmodCwd, env: { HOME: cleanHome, GEMINI_CLI_SYSTEM_SETTINGS_PATH: sysSettings } });
    const u2 = await pickSentinel({ cwd: chmodCwd, env: { HOME: cleanHome, GEMINI_CLI_SYSTEM_SETTINGS_PATH: sysSettings } });
    assert.equal(u1, u2);
    assert.match(u1, /^pdd-disabled-[0-9a-f]{16}$/);
  }
});

test('workflow-chat probes Claude --help with effective agents.json probeEnv rather than raw caller env', async t => {
  const f = await fixture(t, { agent: 'claude' });
  const modernBin = join(f.base, 'modern-bin'), legacyBin = join(f.base, 'legacy-bin'), home = f.ports.env.HOME;
  fs.mkdirSync(modernBin);
  fs.mkdirSync(legacyBin);

  // Caller PATH has modern claude WITH --exclude-dynamic-system-prompt-sections.
  fs.writeFileSync(
    join(modernBin, 'claude'),
    `#!${process.execPath}\nif(process.argv.includes('--help')){process.stdout.write('Options:\\n  --dangerously-skip-permissions\\n  --exclude-dynamic-system-prompt-sections\\n');process.exit(0);}\nif(process.argv[2]==='auth'){process.stdout.write('{"loggedIn":true}');process.exit(0);}\nprocess.stdout.write(JSON.stringify(process.argv.slice(2)));\n`,
    { mode: 0o755 },
  );
  // agents.json entry overrides PATH to legacy claude WITHOUT --exclude-dynamic-system-prompt-sections (and refuses if CLAUDECODE leaked).
  const probeLog = join(f.base, 'probe-env.json');
  fs.writeFileSync(
    join(legacyBin, 'claude'),
    `#!${process.execPath}\nconst fs=require('node:fs');if(process.argv.includes('--help')){fs.writeFileSync(${JSON.stringify(probeLog)},JSON.stringify({PATH:process.env.PATH,CLAUDECODE:process.env.CLAUDECODE??null,CLAUDE_CONFIG_DIR:process.env.CLAUDE_CONFIG_DIR??null,ENTRY_MARK:process.env.ENTRY_MARK??null}));process.stdout.write('Options:\\n  --dangerously-skip-permissions\\n');process.exit(0);}\nif(process.argv[2]==='auth'){process.stdout.write('{"loggedIn":true}');process.exit(0);}\nprocess.stdout.write(JSON.stringify(process.argv.slice(2)));\n`,
    { mode: 0o755 },
  );

  const savedCfg = join(home, '.claude-entry');
  fs.mkdirSync(savedCfg, { recursive: true });
  fs.mkdirSync(join(home, '.config', 'pdd'), { recursive: true });
  fs.writeFileSync(
    join(home, '.config', 'pdd', 'agents.json'),
    JSON.stringify({
      agents: [
        {
          name: 'legacy-claude',
          kind: 'claude',
          command: 'claude',
          env: { PATH: `${legacyBin}:/usr/bin:/bin`, CLAUDE_CONFIG_DIR: savedCfg, ENTRY_MARK: 'from-entry' },
        },
      ],
    }),
  );

  f.ports.env = {
    ...f.ports.env,
    PATH: `${modernBin}:/usr/bin:/bin`,
    CLAUDECODE: '1',
    PDD_AGENT_SESSION: '1',
    CLAUDE_CONFIG_DIR: '/caller/should-not-win',
  };

  const baseHerdr = f.ports.herdr;
  f.ports.herdr = async args => (args[0] === 'pane' && args[1] === 'run' ? baseHerdr([...args.slice(0, 3), args[3].replace("'claude' ", 'claude ')]) : baseHerdr(args));

  const started = await startRun({ name: 'small-change', issue: '17', agent: 'legacy-claude', cwd: f.source, packageRoot }, {
    ...f.ports,
    env: { HOME: home, PATH: `${modernBin}:/usr/bin:/bin`, CLAUDE_CONFIG_DIR: '/caller/should-not-win' },
  });
  assert.equal(started.exitCode, 0, started.message);
  const chat = f.record().chats[0];
  const pane = f.herdr.paneOf(chat);
  assert.doesNotMatch(pane.commands[0], /--exclude-dynamic-system-prompt-sections/, 'must probe legacy claude from agents.json PATH, not modern caller PATH');
  const logged = JSON.parse(fs.readFileSync(probeLog, 'utf8'));
  assert.equal(logged.PATH, `${legacyBin}:/usr/bin:/bin`);
  assert.equal(logged.CLAUDECODE, null);
  assert.equal(logged.CLAUDE_CONFIG_DIR, savedCfg);
  assert.equal(logged.ENTRY_MARK, 'from-entry');

  // Verify chatLaunch.probeEnv directly strips AGENT_MARKER vars even when present on caller env
  const direct = chatLaunch({
    run: f.record(),
    agent: 'claude',
    configDir: savedCfg,
    env: { HOME: home, PATH: `${modernBin}:/usr/bin:/bin`, CLAUDECODE: '1', HERDR_PANE_ID: '%1', PDD_AGENT_SESSION: '1' },
  });
  assert.equal(direct.probeEnv.PATH, `${legacyBin}:/usr/bin:/bin`);
  assert.equal(direct.probeEnv.CLAUDE_CONFIG_DIR, savedCfg);
  assert.equal(direct.probeEnv.CLAUDECODE, undefined);
  assert.equal(direct.probeEnv.HERDR_PANE_ID, undefined);
  assert.equal(direct.probeEnv.PDD_AGENT_SESSION, undefined);
  if (direct.loginFile) fs.rmSync(direct.loginFile, { force: true });

  // Confirm live session once, then simulate ended chat and verify resume also probes with effective agents.json probeEnv
  assert.equal((await openRun({ ref: '17', cwd: f.source }, { ...f.ports, env: { HOME: home, PATH: `${modernBin}:/usr/bin:/bin`, HERDR_ENV: '1' } })).exitCode, 0);
  pane.agent = null;
  const resumed = await openRun({ ref: '17', cwd: f.source }, { ...f.ports, env: { HOME: home, PATH: `${modernBin}:/usr/bin:/bin`, HERDR_ENV: '1' } });
  assert.equal(resumed.exitCode, 0, resumed.message);
  assert.doesNotMatch(pane.commands[1], /--exclude-dynamic-system-prompt-sections/);
});
