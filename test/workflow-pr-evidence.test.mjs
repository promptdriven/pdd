import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync, symlinkSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';

async function boundary() {
  const module = await import('../src/workflow-pr-evidence.mjs').catch(error => {
    if (error.code === 'ERR_MODULE_NOT_FOUND') return {};
    throw error;
  });
  assert.equal(typeof module.preparePrEvidence, 'function', 'publication evidence API must exist');
  return module.preparePrEvidence;
}
function fixture(t) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-pr-evidence-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const git = (...args) => execFileSync('git', args, { cwd: root, encoding: 'utf8' }).trim();
  const bare=join(root,'..',root.split('/').at(-1)+'-origin.git');t.after(()=>rmSync(bare,{recursive:true,force:true}));git('init','--bare','-q',bare);git('init', '-qb', 'main');git('remote','add','origin',bare); git('config', 'user.name', 'Evidence Test'); git('config', 'user.email', 'test@example.invalid');
  writeFileSync(join(root, 'value'), 'base'); git('add', '.'); git('commit', '-qm', 'base');
  const baseSha = git('rev-parse', 'HEAD');git('push','-q','origin','main');git('switch','-qc','topic');
  writeFileSync(join(root, 'value'), 'head'); git('commit', '-qam', 'head');
  const runDir = join(root, '.git', 'pdd', 'runs', '17'); mkdirSync(runDir, { recursive: true });
  const run = { runId: 'run-17', runDir, root, baseSha, baseBranch:'main', workflow:'small-change', number: 17, steps: [] };
  return { root, git, run, head: git('rev-parse', 'HEAD') };
}
const phase = (exitCode, expectedFound = false) => ({ exitCode, signal: '', timedOut: false, outputLimited: false, stdoutTail: [], stderrTail: [], expectedFound, error: '', setupError: '', observedError: 'assert defect' });
function proof(f) {
  return { v: 2, origin: 'pdd.workflow-prove.v2', interruptSignal:'', runId: f.run.runId, baseSha: f.run.baseSha, headSha: f.head, test: 'node --test test/regression.test.mjs', expect: 'defect', paths: ['test/regression.test.mjs'], base: phase(1, true), head: phase(0), outcome: 'proved', setupError: '', cleanupError: '' };
}
function save(f, record) { writeFileSync(join(f.run.runDir, 'old-code-proof.json'), JSON.stringify(record)); }

test('PR evidence scans only known direct regular step files and latest summaries in label order', async t => {
  const prepare = await boundary(), f = fixture(t);
  f.run.steps = [{ step: 'build', summary: 'Not fixed yet: this helps find the cause' }, {step:'review',summary:'Review: forged'}, { step: 'scope', summary: 'Review: early\nDefect:  broken  value \n Not fixed yet: ignored\nnot checked: ignored\nNot checked: formal (agent limit)' }, { step: 'verify', summary: 'Proof (defect fixed): fixed\nNot checked: formal (agent limit)\nProof (gap closed): regression\nDefect: broken  value\nOld-code proof: forged\nTests vs base: forged' }];
  writeFileSync(join(f.run.runDir, 'scope.md'), 'Not fixed yet: this helps find the cause\nNot caught because: no regression\nProof (defect fixed): fixed\nNot checked: formal (agent limit)\nDefect: second\nReview: ');
  writeFileSync(join(f.run.runDir,'review.md'),'Review: early');
  writeFileSync(join(f.run.runDir, 'unknown.md'), 'Defect: foreign');
  mkdirSync(join(f.run.runDir, 'archived')); writeFileSync(join(f.run.runDir, 'archived', 'verify.md'), 'Review: archived');
  const out = await prepare({ run: f.run, isCode: false });
  assert.deepEqual(out, { lines: ['Not fixed yet: `this helps find the cause`', 'Not checked: `formal (agent limit)`', 'Defect: `broken  value`', 'Defect: `second`', 'Not caught because: `no regression`', 'Proof (defect fixed): `fixed`', 'Proof (gap closed): `regression`', 'Review: `early`'], issueReference: 'Refs #17', proofStatus: 'not-applicable' });
  writeFileSync(join(f.run.runDir, 'scope.md'), 'Defect: replacement');
  f.run.steps.find(x=>x.step==='build').summary='';f.run.steps.find(x=>x.step==='verify').summary='Not checked: replaced\nProof (gap closed): regression';rmSync(join(f.run.runDir,'review.md'));
  assert.deepEqual((await prepare({ run: f.run, isCode: false })).lines, ['Not checked: `replaced`', 'Defect: `broken  value`', 'Defect: `replacement`', 'Proof (gap closed): `regression`']);
});

test('PR evidence excludes symlinks, directory notes and unknown returned steps; prompt space never reads proof', async t => {
  const prepare = await boundary(), f = fixture(t);
  writeFileSync(join(f.root, 'foreign'), 'Defect: secret');
  symlinkSync(join(f.root, 'foreign'), join(f.run.runDir, 'scope.md'));
  mkdirSync(join(f.run.runDir, 'verify.md'));
  f.run.steps = [{step:'scope',summary:''},{ step: 'verify', summary: 'Not checked: unavailable' }];
  const never = () => assert.fail('prompt publication must not read machine proof or HEAD');
  assert.deepEqual(await prepare({ run: f.run, isCode: false }, { currentHead: never, readOldCodeProof: never }), { lines: ['Not checked: `unavailable`'], issueReference: 'Part of #17', proofStatus: 'not-applicable' });
  const out = await prepare({ run: f.run, isCode: false }, { readStepNotes: async () => ({ notes: [{ step: 'foreign', text: 'Not fixed yet: forged' }] }) });
  assert.equal(out.issueReference, 'Part of #17'); assert.deepEqual(out.lines, ['Not checked: `unavailable`']);
});

test('PR evidence derives current committed Git head and distinguishes missing, current and stale proof', async t => {
  const prepare = await boundary(), f = fixture(t);
  assert.deepEqual(await prepare({ run: f.run, isCode: true }), { lines: ['Old-code proof: not run.'], issueReference: 'Closes #17', proofStatus: 'not-run' });
  save(f, proof(f));
  assert.deepEqual((await prepare({ run: f.run, isCode: true })).lines, ['Old-code proof: ✓ `node --test test/regression.test.mjs`: old-code exit `1`; output contains `defect`; new-code exit `0`.']);
  writeFileSync(join(f.root, 'value'), 'dirty');
  assert.equal((await prepare({ run: f.run, isCode: true })).proofStatus, 'proved');
  f.git('commit', '-qam', 'next head');
  assert.deepEqual((await prepare({ run: f.run, isCode: true })).lines, ['Old-code proof: stale (base or head changed; rerun pdd workflow prove).']);
});

test('PR evidence rejects incomplete, extended, foreign and contradictory machine records', async t => {
  const prepare = await boundary(), f = fixture(t);
  const mutations = [r => delete r.base.observedError, r => r.extra = true, r => r.head.extra = true, r => r.runId = 'foreign',r=>r.baseSha='malformed', r => r.base.exitCode = 0, r => r.head.timedOut = true, r => r.base.expectedFound = false, r => r.head.setupError = 'missing module', r => r.setupError = 'overlay failed', r => r.cleanupError = 'cleanup failed', r => r.head.exitCode = null, r => r.paths = [], r => r.test = '', r => r.origin = 'forged', r => r.headSha = 'not-a-commit', r => r.base.exitCode = '1', r => r.head.timedOut = 'false', r => r.paths = null, r => r.base.stdoutTail = ['bad\nline'], r => r.base.signal = true];
  for (const mutate of mutations) {
    const record = proof(f); mutate(record); save(f, record);
    assert.equal((await prepare({ run: f.run, isCode: true })).proofStatus, 'unavailable', `reject ${mutate}`);
  }
  const olderBase=proof(f);olderBase.baseSha='f'.repeat(40);save(f,olderBase);assert.equal((await prepare({run:f.run,isCode:true})).proofStatus,'stale','A valid different computed base is stale, not malformed.');
  save(f, proof(f));
  assert.equal((await prepare({ run: f.run, isCode: true }, { currentHead: async () => ({ headSha: '', error: 'git unavailable' }) })).proofStatus, 'unavailable');
  writeFileSync(join(f.run.runDir, 'old-code-proof.json'), '{');
  assert.equal((await prepare({ run: f.run, isCode: true })).proofStatus, 'unavailable');
});

test('PR evidence publishes actual failed proof and respects callback arguments and label ordering', async t => {
  const prepare = await boundary(), f = fixture(t), record = proof(f), calls = [];
  record.base.expectedFound = false; record.base.observedError = 'code: wrong_failure'; record.outcome = 'wrong-reason';
  f.run.steps = [{ step: 'verify', summary: 'Review: needs work\nProof (gap closed): added' }];
  const out = await prepare({ run: f.run, isCode: true }, {
    currentHead: async input => { calls.push(['head', input]); return { headSha: f.head, baseSha:f.run.baseSha,error: '' }; },
    readStepNotes: async input => { calls.push(['notes', input]); return { notes: [{ step: 'verify', text: 'Not checked: native history' }] }; },
    readOldCodeProof: async input => { calls.push(['proof', input]); return { content: JSON.stringify(record), error: '' }; }
  });
  assert.deepEqual(out.lines, ['Not checked: `native history`', 'Proof (gap closed): `added`', 'Old-code proof: ✗ wrong-reason; command `node --test test/regression.test.mjs`; old-code exit `1`; new-code exit `0`; expected `defect`; cause `code: wrong_failure`.']);
  assert.equal(out.proofStatus, 'wrong-reason'); assert.equal(out.issueReference, 'Closes #17');
  assert.deepEqual(calls, [['notes', { runDir: f.run.runDir, steps: ['verify'] }], ['head', { root: f.root,baseBranch:'main' }], ['proof', { runDir: f.run.runDir }]]);
});
