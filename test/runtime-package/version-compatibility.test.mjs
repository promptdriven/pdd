import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runPdd } from '../../src/pdd-cli.mjs';

const capture = () => ({ text: '', write(value) { this.text += value; } });
const cases = [
  { name: 'space', metadata: { version: ' ' }, stdout: ' \n' },
  { name: 'tab', metadata: { version: '\t' }, stdout: '\t\n' },
  { name: 'newline', metadata: { version: '\n' }, stdout: '\n\n' },
  { name: 'ordinary', metadata: { version: '0.1.28' }, stdout: '0.1.28\n' },
  { name: 'padded', metadata: { version: ' 0.1.28 ' }, stdout: ' 0.1.28 \n' },
  { name: 'empty', metadata: { version: '' } },
  { name: 'null', metadata: { version: null } },
  { name: 'missing', metadata: {} },
  { name: 'number', metadata: { version: 28 } },
  { name: 'boolean', metadata: { version: true } },
  { name: 'array', metadata: { version: ['0.1.28'] } },
  { name: 'object', metadata: { version: { value: '0.1.28' } } },
];

test('ordinary versions preserve legacy metadata admission and raw output', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-version-compatibility-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  for (const reader of ['package file', 'injected reader']) {
    for (const flag of ['--version', '-V']) {
      for (const row of cases) await t.test(`${reader} ${flag} ${row.name}`, async () => {
        writeFileSync(join(root, 'package.json'), JSON.stringify(row.metadata));
        const stdout = capture(), stderr = capture();
        const calls = { diagnostic: 0, skills: 0, helper: 0, origin: 0, token: 0, metadata: 0, fetch: 0 };
        const code = await runPdd([flag], {
          packageRoot: root, cwd: root, env: { HOME: root, PATH: '' }, stdout, stderr,
          ...(reader === 'injected reader' ? { readPackageVersion: () => ({ ok: true, version: row.metadata.version }) } : {}),
          pathDiagnostic: () => { calls.diagnostic++; return []; },
          findSkills: () => { calls.skills++; return []; },
          interpreterVersion: { runDetailedVersion: () => { calls.helper++; throw Error('unexpected detailed version'); } },
          interpreterVersionPorts: {
            resolveOrigin: () => { calls.origin++; }, readToken: () => { calls.token++; },
            getMetadata: () => { calls.metadata++; }, fetch: () => { calls.fetch++; },
          },
        });
        const valid = row.stdout !== undefined;
        assert.deepEqual({ code, stdout: stdout.text, stderr: stderr.text }, valid
          ? { code: 0, stdout: row.stdout, stderr: '' }
          : { code: 1, stdout: '', stderr: 'This PDD package has no readable version metadata.\n' });
        assert.deepEqual(calls, { diagnostic: 1, skills: valid ? 1 : 0, helper: 0, origin: 0, token: 0, metadata: 0, fetch: 0 });
      });
    }
  }
});
