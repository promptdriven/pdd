import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { fillHashes, proseSha256 } from '../src/runtime-preflight.mjs';
import { runCheck } from '../src/runtime-client.mjs';

const vectors = JSON.parse(readFileSync(new URL('./fixtures/fill-hash/cases.json', import.meta.url)));
const cli = fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url));
const sink = () => ({ text: '', write(s) { this.text += s; } });
function setup(t, names, placement = vectors.placements[1]) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-fill-vectors-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const repo = join(root, 'repo'), home = join(root, 'home');
  mkdirSync(repo); mkdirSync(home);
  assert.equal(spawnSync('git', ['init', '-q'], { cwd: repo }).status, 0);
  const before = new Map(), cases = new Map();
  for (const name of names) {
    const vector = vectors.cases.find(row => row.name === name);
    const path = name === 'draft' ? vectors.placements[0] : name === 'status-absent' ? placement : `other/${name}.prompt.md`;
    const block = body => `<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${body}\n\`\`\`\n</details>\n`;
    let text = vector.source_bytes ?? `# ${name}\n\nKeep these prose bytes.\n\n` + block(vector.interface_json ?? JSON.stringify(vector.interface, null, 2)).repeat(vector.block_count ?? 1);
    if (vector.source_fixture) assert.equal(text, readFileSync(new URL(`../${vector.source_fixture}`, import.meta.url), 'utf8'), 'source fixture identity');
    if (text.includes('$CURRENT_PROSE_SHA256')) text = text.replace('$CURRENT_PROSE_SHA256', proseSha256(text));
    mkdirSync(dirname(join(repo, path)), { recursive: true }); writeFileSync(join(repo, path), text);
    before.set(path, text); cases.set(path, vector);
  }
  return { root, repo, home, before, cases };
}
function verifyBytes({ repo, before, cases }) {
  for (const [path, original] of before) {
    const actual = readFileSync(join(repo, path), 'utf8');
    if (cases.get(path).changes_hash_only) assert.equal(actual, original.replace('"prose_sha256": ""', `"prose_sha256": "${proseSha256(original)}"`), path);
    else assert.equal(actual, original, path);
  }
}
function advice(message, path, vector) {
  assert.ok(message.includes(path), message);
  for (const word of [...(vector.warning_contains ?? []), ...(vector.refusal_contains ?? [])]) assert.ok(message.includes(word), message);
}
function verifyOutput(text, state, replay) {
  assert.ok(text.includes(summary(replay.counts)), text);
  const warnings = text.split('\n').filter(line => line.startsWith('Warning:'));
  assert.equal(warnings.length, replay.warnings);
  for (const [path, vector] of state.cases) {
    if (vector.warning_contains || vector.refusal_contains) {
      const prefix = vector.outcome === 'warning' ? 'Warning:' : 'Refused:';
      const line = text.split('\n').find(row => row.startsWith(prefix) && row.includes(path));
      assert.ok(line, `${replay.name}: missing ${prefix} ${path}`); advice(line, path, vector);
    }
  }
  if (replay.output_order) assert.deepEqual(text.trim().split('\n').map(line => replay.output_order.find(prefix => line.startsWith(prefix))), replay.output_order);
}
function summary(counts) { return `Hashes: ${counts.filled} filled, ${counts.current} current, ${counts.refused} refused, ${counts.stale} stale.`; }

// Replay the immutable native vectors, including structural and approval controls beside the regression.
test('fill hash native vectors preserve safety while statusless fixtures only warn', async t => {
  const all = setup(t, vectors.cases.map(row => row.name));
  const result = fillHashes({ root: all.repo });
  assert.ok(Array.isArray(result.warnings), 'warnings is always an array');
  for (const [path, vector] of all.cases) {
    const bucket = vector.outcome === 'warning' ? result.warnings : result[vector.outcome];
    assert.deepEqual(bucket.filter(row => row.path === path).map(row => row.path), [path], vector.name);
    if (vector.warning_contains || vector.refusal_contains) advice(bucket.find(row => row.path === path).message, path, vector);
  }
  verifyBytes(all);
  assert.deepEqual(fillHashes({ root: all.repo, files: [] }), { filled: [], current: [], refused: [], stale: [], warnings: [] });
  for (const replay of vectors.replays) {
    const state = setup(t, replay.cases), stdout = sink(), stderr = sink();
    const calls = { fetch: 0, gh: 0 };
    const code = await runCheck({ cwd: state.repo, words: [], options: { '--fill-hash': true } }, {
      env: { HOME: state.home, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, stdout, stderr,
      fetch: async () => { calls.fetch++; assert.fail('network request'); },
      gh: () => { calls.gh++; assert.fail('sign-in'); },
    });
    assert.equal(code, replay.exit_code, replay.name);
    assert.equal(stderr.text, ''); verifyOutput(stdout.text, state, replay);
    assert.deepEqual(calls, { fetch: 0, gh: 0 }); verifyBytes(state);
  }
});

// The public CLI must finish with closed stdin and no Story, auth program or runtime service.
test('fill hash CLI replays succeed beside unrelated prompts in every directory', t => {
  for (const placement of vectors.placements.slice(1)) for (const replay of vectors.replays) {
    const state = setup(t, replay.cases, placement), bin = join(state.root, 'bin'); mkdirSync(bin);
    const git = spawnSync('which', ['git'], { encoding: 'utf8' }); assert.equal(git.status, 0);
    symlinkSync(git.stdout.trim(), join(bin, 'git'));
    const result = spawnSync(process.execPath, [cli, 'check', '--fill-hash'], {
      cwd: state.repo, input: '', timeout: 30000, encoding: 'utf8',
      env: { HOME: state.home, PATH: bin, PDD_RUNTIME_URL: 'http://127.0.0.1:9' },
    });
    assert.equal(result.error, undefined); assert.equal(result.signal, null);
    assert.equal(result.status, replay.exit_code, `${replay.name}: ${result.stdout}\n${result.stderr}`);
    assert.equal(result.stderr, ''); verifyOutput(result.stdout, state, replay);
    verifyBytes(state);
  }
});
