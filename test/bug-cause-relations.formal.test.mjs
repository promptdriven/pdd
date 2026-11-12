import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { recordBugCause } from '../src/workflow-bug-cause.mjs';

// Independent Story oracle: 2 targets × 2 states × 2 quotes × 5 kinds × 4 link choices.
const choices = {
  needs: ['blocked by'],
  'same cause': ['none', 'blocked by'],
  'same class': ['none', 'sub-issue'],
  duplicate: ['duplicate'],
  related: ['none']
};
const links = ['none', 'blocked by', 'sub-issue', 'duplicate'];
async function checkDomain(record) {
  let cases = 0;
  for (const self of [false, true]) for (const open of [false, true])
    for (const quotePresent of [false, true]) for (const [kind, allowed] of Object.entries(choices))
      for (const link of links) {
        cases++;
        const target = self ? 17 : 18;
        const relation = { issue: target, kind, link, source: `issue:${target}`, quote: quotePresent ? 'quoted evidence' : 'absent evidence' };
        const text = `Cause: src/value.mjs#value · Flaw: Fixed value. · Class: value\nRelations: ${JSON.stringify([relation])}`;
        const writes = [];
        const ports = {
          code: { read: async () => ({ content: 'function value() {}' }) },
          issues: { read: async () => ({ json: JSON.stringify({ number: target, state: open ? 'open' : 'closed', title: 'Class: value', body: 'quoted evidence' }) }) },
          links: { ensure: async args => { writes.push(args); return { ok: true }; } }
        };
        const valid = !self && open && quotePresent && allowed.includes(link);
        let error;
        try { await record({ text, repository: 'owner/repo', number: 17, root: '/repo' }, ports); }
        catch (caught) { error = caught; }
        const label = JSON.stringify({ self, open, quotePresent, kind, link });
        assert.equal(error?.code, valid ? undefined : 'bug-cause-invalid', label);
        assert.equal(writes.length, valid && link !== 'none' ? 1 : 0, label);
        if (writes.length) assert.deepEqual(writes[0], { repository: 'owner/repo', number: 17, target, kind: link }, label);
      }
  return cases;
}

test('bounded Story rules: 160 relation combinations and all quotes before writes', async () => {
  assert.equal(await checkDomain(recordBugCause), 160);
  const writes = [];
  const rows = [18, 19].map((issue, index) => ({ issue, kind: 'needs', link: 'blocked by', source: `issue:${issue}`, quote: index ? 'missing' : 'present' }));
  await assert.rejects(recordBugCause({ text: `Cause: value.mjs#value · Flaw: Fixed. · Class: value\nRelations: ${JSON.stringify(rows)}`, repository: 'owner/repo', number: 17, root: '/repo' }, {
    code: { read: async () => ({ content: 'value' }) },
    issues: { read: async ({ number }) => ({ json: JSON.stringify({ number, state: 'open', title: 'present', body: '' }) }) },
    links: { ensure: async args => { writes.push(args); return { ok: true }; } }
  }), { code: 'bug-cause-invalid' });
  assert.equal(writes.length, 0);
});

test('issue #2841: malformed relation kinds are rejected before any link writes', async () => {
  for (const kind of [['needs'], ['related'], [], ['needs', 'related'], null, 1, false, {}]) {
    const writes = [];
    const rows = [
      { issue: 18, kind: 'needs', link: 'blocked by', source: 'issue:18', quote: 'present' },
      { issue: 19, kind, link: kind?.[0] === 'related' ? 'none' : 'blocked by', source: 'issue:19', quote: 'present' }
    ];
    await assert.rejects(recordBugCause({ text: `Cause: value.mjs#value · Flaw: Fixed. · Class: value\nRelations: ${JSON.stringify(rows)}`, repository: 'owner/repo', number: 17, root: '/repo' }, {
      code: { read: async () => ({ content: 'value' }) },
      issues: { read: async ({ number }) => ({ json: JSON.stringify({ number, state: 'open', title: 'present', body: '' }) }) },
      links: { ensure: async args => { writes.push(args); return { ok: true }; } }
    }), { code: 'bug-cause-invalid' }, JSON.stringify(kind));
    assert.deepEqual(writes, [], JSON.stringify(kind));
  }
});

test('bounded check detects a planted missing quote check', async () => {
  const dir = await mkdtemp(join(tmpdir(), 'pdd-2841-control-'));
  try {
    const original = await readFile(new URL('../src/workflow-bug-cause.mjs', import.meta.url), 'utf8');
    const needle = 'if (!evidence.some(value => value.includes(row.quote)))';
    assert.ok(original.includes(needle), 'control mutation site exists');
    const mutant = join(dir, 'mutant.mjs');
    await writeFile(mutant, original.replace(needle, 'if (false)'));
    const { recordBugCause: mutated } = await import(pathToFileURL(mutant));
    await assert.rejects(checkDomain(mutated), error => error instanceof assert.AssertionError);
  } finally { await rm(dir, { recursive: true, force: true }); }
});
