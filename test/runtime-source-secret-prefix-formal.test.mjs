import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { captureSource, sourceFilePort } from '../src/runtime-preflight.mjs';
import { harbor } from './runtime-fake.mjs';

// Story Rules to check: secret-looking generated paths refuse even below missing
// folders, and unsafe missing paths refuse on stat. Expected classes are supplied
// by the approved examples, independently of the implementation's secret matcher.
const pairs = [ ['.env', 'config.txt'], ['id_rsa', 'identity.txt'],
  ['server.pem', 'server.crt'], ['secrets/x.md', 'public/x.md'] ];
const payload = Buffer.from('SYNTHETIC prepared bytes\0\n');
function entryBytes(tar, path) {
  for (let offset = 0; offset + 512 <= tar.length;) {
    const header = tar.subarray(offset, offset + 512);
    const name = header.subarray(0, 100).toString().replace(/\0.*$/s, '');
    const size = parseInt(header.subarray(124, 136).toString().trim(), 8) || 0;
    if (name === path) {
      assert.equal(header[156], '0'.charCodeAt(0));
      return tar.subarray(offset + 512, offset + 512 + size);
    }
    offset += 512 + Math.ceil(size / 512) * 512;
  }
  assert.fail(`prepared output absent from archive: ${path}`);
}

test('LINK formal secret prefixes: all 108 bounded stat/prepared-capture worlds obey privacy before absence', t => {
  const { repo } = harbor(t);
  let worlds = 0, refused = 0, allowed = 0;
  for (const pair of pairs) for (const depth of [0, 1, 2]) {
    // A filesystem can only have a contiguous existing ancestor prefix. For
    // each depth enumerate every such prefix, including none and all.
    const ancestors = depth + pair[0].split('/').length - 1;
    for (let existing = 0; existing <= ancestors; existing++)
      for (const secret of [true, false]) for (const operation of ['stat', 'capture']) {
        // Separate worlds with no persistent generated files; root is the fixed
        // existing Git-repository ancestor and isn't part of the variable bound.
        for (const name of ['prefix0', '.env', 'id_rsa', 'server.pem', 'secrets', 'config.txt', 'identity.txt', 'server.crt', 'public'])
          rmSync(join(repo, name), { recursive: true, force: true });
        const path = [...Array.from({ length: depth }, (_, i) => `prefix${i}`), pair[secret ? 0 : 1]].join('/');
        const components = path.split('/');
        if (existing) mkdirSync(join(repo, ...components.slice(0, existing)), { recursive: true });
        const label = JSON.stringify({ path, existing, operation, secret });
        let archive;
        const action = operation === 'stat'
          ? () => sourceFilePort(repo).stat({ path })
          : () => { archive = captureSource(repo, { tests: [], prepareSource: () => [{ path, bytes: payload }] }); return archive; };
        if (secret) {
          assert.throws(action, error => error.exitCode === 4 && /name looks like a secret/.test(error.message), label);
          assert.equal(archive, undefined, `no archive may escape: ${label}`);
          refused++;
        } else {
          let result;
          assert.doesNotThrow(() => { result = action(); }, label);
          if (operation === 'stat') assert.equal(result.exists, false, label);
          else assert.deepEqual(entryBytes(result.tar, path), payload, label);
          allowed++;
        }
        worlds++;
      }
  }
  // 3 leaf patterns * (1+2+3) + 1 folder pattern * (2+3+4)
  // = 27 prefix states * 2 eligibility classes * 2 public operations.
  assert.deepEqual({ worlds, refused, allowed }, { worlds: 108, refused: 54, allowed: 54 });
  t.diagnostic(`worlds=${worlds} refused=${refused} allowed=${allowed}; 27 prefix states per class, stat and prepared capture`);
});
