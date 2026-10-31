import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { captureSource, sourceFilePort } from '../src/runtime-preflight.mjs';
import { harbor } from './runtime-fake.mjs';

// Story: user_stories/read-in-repo-links.md, Rules to check / AC1, AC3.
// Exhaustive finite domain: two labelled link nodes, each with six destinations;
// direct/folder spelling x visible/ignored/secret authored spelling x visible/ignored
// regular terminal = 6^2 * 2 * 3 * 2 = 432 worlds. No concurrent mutation.
const destinations = ['safe', 'secret', 'missing', 'outside', 'a', 'b'];
const payload = Buffer.from('bounded linked bytes\0\n');

// Independent graph oracle: only a visible nonsecret authored path whose finite
// walk terminates at the visible safe regular file may contribute bytes.
function allowed(edges, authored, terminalVisible) {
  if (authored !== 'visible' || !terminalVisible) return false;
  const visited = new Set();
  let node = 'a';
  while (node === 'a' || node === 'b') {
    if (visited.has(node)) return false;
    visited.add(node);
    node = edges[node];
  }
  return node === 'safe';
}

function archiveEntry(tar, authored) {
  for (let offset = 0; offset < tar.length;) {
    const header = tar.subarray(offset, offset + 512);
    const name = header.subarray(0, 100).toString().replace(/\0.*$/s, '');
    const size = parseInt(header.subarray(124, 136).toString().trim(), 8) || 0;
    if (name === authored) return {
      type: header[156], mode: parseInt(header.subarray(100, 108).toString(), 8),
      bytes: tar.subarray(offset + 512, offset + 512 + size),
    };
    offset += 512 + Math.ceil(size / 512) * 512;
  }
  assert.fail(`missing authored archive entry ${authored}`);
}

test('LINK formal bounded: all 432 authored eligibility and two-node resolution worlds obey the Story oracle', t => {
  const { repo, sandbox } = harbor(t);
  writeFileSync(join(sandbox, 'outside.md'), payload);
  mkdirSync(join(sandbox, 'outside-dir'));
  writeFileSync(join(sandbox, 'outside-dir/leaf.md'), payload);
  let worlds = 0, accepted = 0, refused = 0;
  for (const kind of ['direct', 'folder']) for (const authored of ['visible', 'ignored', 'secret'])
    for (const terminalVisible of [true, false]) for (const a of destinations) for (const b of destinations) {
      rmSync(join(repo, 'world'), { recursive: true, force: true });
      mkdirSync(join(repo, 'world/secrets'), { recursive: true });
      const folder = kind === 'folder';
      const names = { a: authored === 'secret' ? '.env' : (folder ? 'a' : 'a.md'), b: folder ? 'b' : 'b.md',
        safe: folder ? 'safe' : 'safe.md', secret: folder ? 'secrets/.env' : 'secrets/.env',
        missing: folder ? 'missing' : 'missing.md', outside: folder ? '../../outside-dir' : '../../outside.md' };
      for (const terminal of ['safe', 'secret']) {
        if (folder) mkdirSync(join(repo, 'world', names[terminal]), { recursive: true });
        writeFileSync(join(repo, 'world', names[terminal], ...(folder ? ['leaf.md'] : [])), payload);
      }
      const edges = { a, b };
      for (const node of ['a', 'b']) symlinkSync(names[edges[node]], join(repo, 'world', names[node]));
      const path = `world/${names.a}${folder ? '/leaf.md' : ''}`;
      const terminalPath = `world/${names.safe}${folder ? '/leaf.md' : ''}`;
      writeFileSync(join(repo, '.gitignore'), [
        ...(authored === 'ignored' ? [`/world/${names.a}`] : []),
        ...(!terminalVisible ? [`/${terminalPath}`] : []),
      ].join('\n') + '\n');
      writeFileSync(join(repo, 'pdd-source.json'), JSON.stringify({ include: [path] }));
      const label = JSON.stringify({ kind, authored, terminalVisible, edges });
      const port = sourceFilePort(repo);
      if (allowed(edges, authored, terminalVisible)) {
        let read, stat, capture;
        assert.doesNotThrow(() => { read = port.read({ path }); }, label);
        assert.equal(read.content, payload.toString('utf8'), label);
        assert.doesNotThrow(() => { stat = port.stat({ path }); }, label);
        assert.equal(stat.exists, true, label); assert.equal(stat.is_symlink, false, label);
        assert.equal(stat.size, payload.length, label);
        assert.doesNotThrow(() => { capture = captureSource(repo, { tests: ['tests/place-order.json'] }); }, label);
        const entry = archiveEntry(capture.tar, path);
        assert.equal(entry.type, '0'.charCodeAt(0), label);
        assert.equal(entry.mode, 0o600, label); assert.deepEqual(entry.bytes, payload, label);
        accepted++;
      } else {
        assert.throws(() => port.read({ path }), undefined, label);
        assert.throws(() => port.stat({ path }), undefined, label);
        assert.throws(() => captureSource(repo, { tests: ['tests/place-order.json'] }), undefined, label);
        refused++;
      }
      worlds++;
    }
  assert.deepEqual({ worlds, accepted, refused }, { worlds: 432, accepted: 14, refused: 418 });
  t.diagnostic(`worlds=${worlds} accepted=${accepted} refused=${refused}; read/stat/capture checked in every world`);
});
