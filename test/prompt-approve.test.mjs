import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { approvePromptText, runApprove } from '../src/prompt-approve.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
import { approveRun, stepDone } from '../src/workflow-runner.mjs';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';
import { PLACE, harbor, root, sink } from './runtime-fake.mjs';

const GOLDEN = 'd5958a8577dcb8dd6ff25c8df4ea3b85e8c5dcf7c16863d8e502a24095db6abb';
const asDraft = text => text.replace('"status": "approved"', '"status": "draft"').replace(GOLDEN, '');

async function approve(setup, words, answer, { tty = true } = {}) {
  const ports = { stdout: sink(), stderr: sink(), stdin: Readable.from(answer === null ? [] : [`${answer}\n`]), interactive: tty };
  const code = await runApprove({ words, cwd: setup.repo }, ports);
  return { code, out: ports.stdout.text, err: ports.stderr.text };
}

// Wrong: an agent (no terminal) approves a prompt, or approve changes the file without a person's yes.
test('APPROVE1: pdd approve refuses without a real terminal and changes nothing', async t => {
  const setup = harbor(t, repo => { const file = join(repo, PLACE); writeFileSync(file, asDraft(readFileSync(file, 'utf8'))); });
  const before = readFileSync(join(setup.repo, PLACE), 'utf8');
  const result = await approve(setup, [PLACE], 'y', { tty: false });
  assert.equal(result.code, 2);
  assert.match(result.err, /pdd approve is for a person at a terminal\. Ask the person to run: pdd approve prompts\/place_order\.prompt\.md/);
  assert.equal(readFileSync(join(setup.repo, PLACE), 'utf8'), before);
});

// Wrong: the person approves without seeing the shapes, or approve rewrites other bytes or leaves a stale hash.
test('APPROVE2: pdd approve shows the interface, asks y/n, and on y sets approved and fills the hash, nothing else', async t => {
  const setup = harbor(t, repo => { const file = join(repo, PLACE); writeFileSync(file, asDraft(readFileSync(file, 'utf8'))); });
  const draft = readFileSync(join(setup.repo, PLACE), 'utf8');
  const result = await approve(setup, [PLACE], 'y');
  assert.equal(result.code, 0, result.err);
  for (const text of ['prompts/place_order.prompt.md (draft)', 'Operation place_order', 'Input:', '  customerName: string (at least 1 character)',
    '  items: a list (at least 1 item) of:', '    size: "S", "M" or "L"', '    quantity: integer, 1 to 20', 'Result:', '  totalCents: integer',
    'Errors: unknown-item', 'Approve prompts/place_order.prompt.md? y/n ', 'Approved prompts/place_order.prompt.md.']) {
    assert.ok(result.out.includes(text), `${text}\n---\n${result.out}`);
  }
  const after = readFileSync(join(setup.repo, PLACE), 'utf8');
  assert.equal(after, draft.replace('"status": "draft"', '"status": "approved"').replace('"prose_sha256": ""', `"prose_sha256": "${GOLDEN}"`));
  assert.equal(proseSha256(after), GOLDEN);
  assert.equal((await approve(setup, [PLACE], 'y')).out.trim(), 'prompts/place_order.prompt.md is already approved and current.');
});

// Wrong: anything but a clear yes approves, or a prompt with schema problems gets approved.
test('APPROVE3: only y or yes approves; a stale approval asks again; schema problems refuse (exit 4)', async t => {
  const setup = harbor(t, repo => { const file = join(repo, PLACE); writeFileSync(file, asDraft(readFileSync(file, 'utf8'))); });
  const draft = readFileSync(join(setup.repo, PLACE), 'utf8');
  for (const answer of ['n', '', 'maybe', null]) {
    const result = await approve(setup, [PLACE], answer);
    assert.equal(result.code, 1, String(answer)); assert.match(result.out, /Not approved\. Nothing changed\./);
    assert.equal(readFileSync(join(setup.repo, PLACE), 'utf8'), draft);
  }
  assert.equal((await approve(setup, [PLACE], 'YES')).code, 0);
  const file = join(setup.repo, PLACE);
  writeFileSync(file, readFileSync(file, 'utf8').replace('Use this menu.', 'Use this menu now.'));
  const stale = await approve(setup, [PLACE], 'y');
  assert.equal(stale.code, 0); assert.match(stale.out, /The text changed after it was approved\./);
  assert.equal(proseSha256(readFileSync(file, 'utf8')), JSON.parse(readFileSync(file, 'utf8').match(/```json\n([\s\S]*?)\n```/)[1]).prose_sha256);
  writeFileSync(file, readFileSync(file, 'utf8').replace('"status": "approved"', '"status": "draft"').replace('"minLength": 1', '"minLength": 1, "anyOf": []'));
  const broken = await approve(setup, [PLACE], 'y');
  assert.equal(broken.code, 4); assert.match(broken.out, /graph-schema-unsupported-keyword[\s\S]*\/entries\/0\/input_schema\/properties\/customerName/);
  assert.match(readFileSync(file, 'utf8'), /"status": "draft"/);
  const missing = await approve(setup, ['prompts/nope.prompt.md'], 'y');
  assert.equal(missing.code, 2); assert.match(missing.err, /prompts\/nope\.prompt\.md is not a Git-visible \*\.prompt\.md file/);
});

const section = (out, title) => { const lines = out.split('\n'), at = lines.findIndex(text => text.startsWith(title)); return at < 0 ? [] : lines.slice(at, lines.findIndex((text, index) => index > at && text.startsWith('Approve '))); };

// Wrong: the person approves a prose change that the screen does not show (round-2 tester, Oct 27: only the interface was shown).
test('APPROVE6: pdd approve shows the prose changes since the last approved version in Git, short, before the question', async t => {
  const setup = harbor(t), file = join(setup.repo, PLACE), approved = readFileSync(file, 'utf8');
  const commit = spawnSync('git', ['log', '-1', '--format=%H'], { cwd: setup.repo, encoding: 'utf8' }).stdout.trim().slice(0, 12);
  writeFileSync(file, asDraft(approved));
  const same = await approve(setup, [PLACE], 'n');
  assert.deepEqual(section(same.out, 'Text'), [`Text: the same as the last approved version (${commit}).`]);
  writeFileSync(file, asDraft(approved).replace('Use this menu.', 'Use this menu now.'));
  const changed = await approve(setup, [PLACE], 'y');
  assert.equal(changed.code, 0, changed.err);
  assert.deepEqual(section(changed.out, 'Text'), [`Text changes since the last approved version (${commit}):`, '', '  - Use this menu. Prices are in whole cents.',
    '  + Use this menu now. Prices are in whole cents.', '']);
  assert.ok(changed.out.indexOf('Operation place_order') < changed.out.indexOf('Text changes'));
  const rules = Array.from({ length: 45 }, (_, index) => `Rule ${index + 1}: keep it short.`).join('\n');
  writeFileSync(file, readFileSync(file, 'utf8').replace('"status": "approved"', '"status": "draft"').replace('Use this menu now.', `Use this menu now.\n${rules}`));
  const long = section((await approve(setup, [PLACE], 'n')).out, 'Text');
  assert.equal(long.length, 42);
  assert.match(long.at(-1), new RegExp(`^… \\d+ more lines not shown\\. See all of them with: git diff ${commit} -- prompts/place_order\\.prompt\\.md$`));
});

// Wrong: a new prompt shows no text, or a long one floods the screen, or terminal codes hide words from the person.
test('APPROVE7: with no approved version pdd approve shows the whole prose, at most 40 lines, with no terminal codes', async t => {
  const extra = Array.from({ length: 50 }, (_, index) => `Rule ${index + 1}.`).join('\n');
  const setup = harbor(t, repo => { const file = join(repo, PLACE); writeFileSync(file, asDraft(readFileSync(file, 'utf8')).replace('Use this menu.', `Use this \x1b[8mhidden\x1b[0m menu.\n${extra}`)); });
  const result = await approve(setup, [PLACE], 'n');
  assert.equal(result.code, 1);
  const shown = section(result.out, 'Text');
  assert.deepEqual(shown.slice(0, 3), ['Text (no approved version in Git, so all of it):', '  # Place a Harbor Coffee order', '']);
  assert.ok(shown.includes('  Use this hidden menu.'), shown.join('\n'));
  assert.equal(shown.length, 42);
  assert.match(shown.at(-1), /^… \d+ more lines not shown\. Read the whole file: prompts\/place_order\.prompt\.md$/);
  assert.equal(result.out.includes('\x1b'), false);
});

// Wrong: the text edit touches a nested "status" or drops formatting.
test('APPROVE4: the edit changes only the top-level status and prose_sha256 values', () => {
  const text = '# P\n\n<details><summary>Runtime interface</summary>\n\n```json\n{"status": "draft", "prose_sha256": "", "entries": [{"operation": "x", "input_schema": {"type": "object", "properties": {"status": {"type": "string", "const": "draft"}}, "required": [], "additionalProperties": false}, "result_schema": {"type": "string"}, "errors": []}], "calls": [], "resources": [], "limits": {"max_steps": 1, "max_model_calls": 1}}\n```\n</details>\n';
  const next = approvePromptText(text);
  assert.equal(next, text.replace('{"status": "draft", "prose_sha256": ""', `{"status": "approved", "prose_sha256": "${proseSha256(text)}"`));
});

// Wrong: the CLI route is missing, or it runs the approval with no terminal.
test('APPROVE5: pdd approve is a CLI route with help, and refuses in a pipe', t => {
  const setup = harbor(t), env = { ...process.env, HOME: setup.home };
  delete env.CLAUDE_CONFIG_DIR;
  const pdd = (...args) => spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), ...args], { cwd: setup.repo, env, encoding: 'utf8', input: 'y\n', timeout: 20000 });
  const help = pdd('approve', '--help');
  assert.equal(help.status, 0); assert.match(help.stdout, /pdd approve PROMPT/);
  const piped = pdd('approve', PLACE);
  assert.equal(piped.status, 2); assert.match(piped.stderr, /pdd approve is for a person at a terminal/);
  assert.equal(pdd('approve').status, 2);
});

const CONTRACT_DOC = '# Shared contracts\n\n### row\n\n```json\n{"type":"object","properties":{"itemId":{"type":"string"},"size":{"type":"string","enum":["S","M","L"]},"quantity":{"type":"integer","minimum":1,"maximum":20}},"required":["itemId","size","quantity"],"additionalProperties":false}\n```\n';
const CONTRACT_PROMPT = ref => `# Order\n\n## Dependencies\n\n- [Shared contracts](../contracts/x.md)\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n{"status": "draft", "prose_sha256": "", "entries": [{"operation": "place_order", "input_schema": {"type": "object", "properties": {"row": {"$contract": "${ref}"}}, "required": ["row"], "additionalProperties": false}, "result_schema": {"type": "integer"}, "errors": []}], "calls": [], "resources": [], "limits": {"max_steps": 1, "max_model_calls": 1}, "conventions": []}\n\`\`\`\n</details>\n`;

// Wrong: pdd approve or pdd workflow approve rejects a valid {"$contract": ...} schema with graph-schema-type-invalid ("has no type") or rewrites the prompt's own unexpanded bytes.
test('APPROVE8: pdd approve (--said) and pdd workflow approve expand $contract references before schema validation and keep the prompt bytes', async t => {
  const draft = CONTRACT_PROMPT('contracts/x.md#row');
  const expected = draft.replace('"status": "draft", "prose_sha256": ""', `"status": "approved", "prose_sha256": "${proseSha256(draft)}"`);
  const setup = harbor(t, repo => {
    mkdirSync(join(repo, 'contracts'), { recursive: true });
    writeFileSync(join(repo, 'contracts/x.md'), CONTRACT_DOC);
    writeFileSync(join(repo, PLACE), draft);
  });
  const ports = { stdout: sink(), stderr: sink(), stdin: Readable.from([]), interactive: false };
  const code = await runApprove({ words: [PLACE], cwd: setup.repo, said: 'I approve' }, ports);
  assert.equal(code, 0, `${ports.stderr.text}\n${ports.stdout.text}`);
  assert.equal(readFileSync(join(setup.repo, PLACE), 'utf8'), expected);

  const f = await fixture(t, { name: 'feature' });
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  mkdirSync(join(run.root, 'contracts'), { recursive: true });
  mkdirSync(join(run.root, 'prompts'), { recursive: true });
  writeFileSync(join(run.root, 'contracts/x.md'), CONTRACT_DOC);
  writeFileSync(join(run.root, PLACE), draft);
  for (const step of ['understand', 'visual', 'prompt-story']) {
    f.tick();
    assert.equal((await stepDone({ step, summary: 'Draft prompt with contract ref', cwd: run.root }, f.agentPorts())).exitCode, 0);
  }
  f.herdr.idle();
  const out = await approveRun({ ref: '17', cwd: run.root, said: 'I approve' }, f.agentPorts());
  assert.equal(out.exitCode, 0, out.message);
  assert.equal(readFileSync(join(run.root, PLACE), 'utf8'), expected);
});

// Wrong: a broken $contract reference reports "has no type" (graph-schema-type-invalid) instead of the contract problem code.
test('APPROVE9: broken $contract references report the lint contract problem code in pdd approve and pdd workflow approve', async t => {
  for (const ref of ['contracts/missing.md#row', 'contracts/x.md#missing']) {
    const draft = CONTRACT_PROMPT(ref);
    const setup = harbor(t, repo => {
      mkdirSync(join(repo, 'contracts'), { recursive: true });
      writeFileSync(join(repo, 'contracts/x.md'), CONTRACT_DOC);
      writeFileSync(join(repo, PLACE), draft);
    });
    const ports = { stdout: sink(), stderr: sink(), stdin: Readable.from([]), interactive: false };
    const code = await runApprove({ words: [PLACE], cwd: setup.repo, said: 'I approve' }, ports);
    assert.equal(code, 4, ref);
    assert.match(ports.stdout.text, /contract-missing/);
    assert.doesNotMatch(ports.stdout.text + ports.stderr.text, /graph-schema-type-invalid|has no type/);
    assert.equal(readFileSync(join(setup.repo, PLACE), 'utf8'), draft);

    const f = await fixture(t, { name: 'feature' });
    assert.equal((await f.run()).exitCode, 0);
    const run = f.record();
    mkdirSync(join(run.root, 'contracts'), { recursive: true });
    mkdirSync(join(run.root, 'prompts'), { recursive: true });
    writeFileSync(join(run.root, 'contracts/x.md'), CONTRACT_DOC);
    writeFileSync(join(run.root, PLACE), draft);
    for (const step of ['understand', 'visual', 'prompt-story']) {
      f.tick();
      assert.equal((await stepDone({ step, summary: 'Draft prompt with broken contract ref', cwd: run.root }, f.agentPorts())).exitCode, 0);
    }
    f.herdr.idle();
    const out = await approveRun({ ref: '17', cwd: run.root, said: 'I approve' }, f.agentPorts());
    assert.notEqual(out.exitCode, 0, ref);
    assert.match(out.message, /contract-missing/);
    assert.doesNotMatch(out.message, /graph-schema-type-invalid|has no type/);
    assert.equal(readFileSync(join(run.root, PLACE), 'utf8'), draft);
  }
});
