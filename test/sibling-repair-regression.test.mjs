import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { join } from 'node:path';
import { interfaceBlocks } from '../src/runtime-preflight.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { runContracts } from '../src/contracts.mjs';
import { harbor, fakeRuntime, portsFor, PLACE, sink } from './runtime-fake.mjs';

const ONE = 'tests/place-order.json';
const MISSING = 'prompts/not-yet.prompt.md';
const write = (root, path, text) => {
  fs.mkdirSync(join(root, path, '..'), { recursive: true });
  fs.writeFileSync(join(root, path), text);
};

// Accepted client advisory forwarding applies to explicit text lint even when
// the selected lint result is refused or remote admission stops the request.
for (const outcome of ['passed', 'refused', 'not-run']) {
  test(`SIBLING repair: explicit text lint retains capture advisories (${outcome})`, async t => {
    const s = harbor(t);
    const sibling = JSON.parse(fs.readFileSync(join(s.repo, ONE), 'utf8'));
    sibling.steps.forEach(step => { step.entry_path = MISSING; });
    write(s.repo, 'tests/sibling.json', JSON.stringify(sibling));
    const fake = await fakeRuntime(t, (entry, f) => {
      assert.equal(entry.command, 'lint', 'explicit lint must not submit checks');
      if (outcome === 'not-run') return { status: 403, json: { code: 'no-cloud-access', message: 'Synthetic access refusal.' } };
      const answer = f.lint(entry.request.requestId);
      if (outcome === 'refused') answer.result.problems = [{ code: 'synthetic-refusal', file: ONE, severity: 'error', message: 'Synthetic selected test refusal.' }];
      if (outcome === 'refused') answer.result.tests = [{ path: ONE, verdict: 'refused' }];
      return { status: 200, json: answer };
    });
    const { ports } = portsFor({ HOME: s.home, PDD_STATE_DIR: s.state, PDD_RUNTIME_URL: fake.origin });
    const code = await runCheck({ cwd: s.repo, words: [ONE], options: { '--lint': true } }, ports);
    assert.equal(code, { passed: 0, refused: 4, 'not-run': 5 }[outcome], ports.stderr.text);
    assert.equal(fake.posts.length, 1);
    assert.equal(fake.posts[0].request.complete, true);
    assert.match(ports.stderr.text, /Warning: user_stories\/place-order\.md: footprint unavailable:.*not-yet\.prompt\.md/,
      'text lint must emit the unavailable footprint and its actual cause');
    assert.equal(ports.stdout.text.includes('footprint unavailable'), false, 'capture advice uses the existing stderr warning stream');
  });
}

// Catalog users are verified evidence, never an exhaustive list when a prompt
// was skipped unread or could not resolve its references. Preserve known users.
for (const known of [false, true]) for (const failure of ['12MiB', '2GiB', 'unresolved', 'sibling']) {
  test(`SIBLING repair: catalog marks ${known ? 'known' : 'empty'} users incomplete after ${failure} consumer`, t => {
    const s = harbor(t), target = 'contracts/visible.json#', ignored = 'prompts/ignored.prompt.md';
    const original = fs.readFileSync(join(s.repo, PLACE), 'utf8');
    const block = interfaceBlocks(original)[0], program = JSON.parse(block[1]);
    write(s.repo, 'contracts/visible.json', JSON.stringify(program.entries[0].input_schema));
    if (known) {
      program.entries[0].input_schema = { $contract: target };
      write(s.repo, PLACE, original.slice(0, block.indices[1][0]) + JSON.stringify(program) + original.slice(block.indices[1][1]));
    }
    let reads = 0;
    if (failure === 'sibling') {
      const sibling = JSON.parse(fs.readFileSync(join(s.repo, ONE), 'utf8'));
      sibling.initial_world = { $seed: 'contracts/missing-world.json' };
      write(s.repo, 'tests/sibling.json', JSON.stringify(sibling));
    } else if (failure === 'unresolved') {
      const broken = JSON.parse(block[1]);
      broken.entries[0].input_schema = { $contract: 'contracts/missing.json#' };
      write(s.repo, ignored, original.slice(0, block.indices[1][0]) + JSON.stringify(broken) + original.slice(block.indices[1][1]));
    } else {
      write(s.repo, ignored, '');
      fs.truncateSync(join(s.repo, ignored), failure === '12MiB' ? 12_582_912 : 2_147_483_649);
      const originals = { openSync: fs.openSync, readFileSync: fs.readFileSync };
      for (const method of Object.keys(originals)) fs[method] = (path, ...args) => {
        if (path === join(s.repo, ignored)) { reads++; assert.fail('oversized discovery consumer must remain unread'); }
        return originals[method](path, ...args);
      };
      syncBuiltinESMExports();
      t.after(() => { Object.assign(fs, originals); syncBuiltinESMExports(); });
    }
    const stdout = sink(), stderr = sink();
    assert.equal(runContracts({ cwd: s.repo }, { env: { HOME: s.home, PDD_STATE_DIR: s.state }, stdout, stderr }), 0, stderr.text);
    if (failure === 'sibling') assert.match(stdout.text, /footprint unavailable.*missing-world\.json/);
    else assert.match(stderr.text, /ignored\.prompt\.md:.*(?:unavailable|too big)/);
    const record = stdout.text.split('\n').find(line => line.startsWith(`${target}  `));
    assert.ok(record, 'independent record remains listed');
    const users = /  users: (.*?)  Stories:/.exec(record)?.[1];
    assert.match(users, /unavailable|incomplete/, 'unread consumer prevents a complete no-user or known-user claim');
    assert.equal(users.includes(PLACE), known, 'retain every verified user without inventing one');
    assert.equal(/\bnone\b/.test(users), false, 'incomplete discovery cannot prove no users');
    assert.equal(reads, 0);
  });
}
