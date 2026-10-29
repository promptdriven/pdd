import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, rm, mkdir, symlink } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { resolveWorkflowIssue, prepareWorkflowPr, publishWorkflowPr, reconcileWorkflowPr } from '../src/workflow-github.mjs';

const headSha = 'a'.repeat(40);
function row(intent, extra = {}) { return { number: 42, url: 'https://github.com/Acme/Project/pull/42', state: 'OPEN', headRefName: intent.headBranch, baseRefName: intent.baseBranch, headRefOid: intent.headSha, mergeCommit: null, body: `<!-- ${intent.marker} -->\n`, isCrossRepository: false, headRepository: { name: 'Project' }, headRepositoryOwner: { login: 'Acme' }, ...extra }; }
async function fixture(t) {
  const cwd = await mkdtemp(join(tmpdir(), 'pdd-github-')); t.after(() => rm(cwd, { recursive: true, force: true }));
  const calls = [], state = { origin: 'git@github.com:Acme/Project.git', pushOrigin: 'https://github.com/Acme/Project.git', dirty: '', branch: 'topic/feature', headSha, count: '1', rows: [], remoteHead: null, issue: { number: 12, html_url: 'https://github.com/Acme/Project/issues/12', title: 'Real issue', body: 'Authored body' } };
  const ports = { async execFile(file, args, options) { calls.push({ file, args: [...args], options }); assert.equal(options.cwd, cwd); const key = `${file} ${args.join(' ')}`;
    if (file === 'git' && args[0] === 'remote' && args[1] === 'get-url') return { stdout: args[2] === '--push' ? state.pushOrigin : state.origin };
    if (file === 'gh' && args[0] === 'repo') return { stdout: JSON.stringify({ nameWithOwner: 'Acme/Project', defaultBranchRef: { name: 'main' }, url: 'https://github.com/Acme/Project' }) };
    if (file === 'gh' && args[0] === 'api') return { stdout: JSON.stringify(state.issue) };
    if (file === 'git' && args[0] === 'check-ref-format') return { stdout: '' };
    if (key === 'git rev-parse --show-toplevel') return { stdout: cwd };
    if (file === 'git' && args[0] === 'status') return { stdout: state.dirty };
    if (file === 'git' && args[0] === 'symbolic-ref') return { stdout: state.branch };
    if (key === 'git rev-parse --verify HEAD') return { stdout: state.headSha };
    if (file === 'git' && args[0] === 'rev-parse') return { stdout: 'c'.repeat(40) };
    if (file === 'git' && args[0] === 'rev-list') return { stdout: state.count };
    if (file === 'git' && args[0] === 'log') return { stdout: 'Implement selected feature' };
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'list') return { stdout: JSON.stringify(state.rows) };
    if (file === 'git' && args[0] === 'ls-remote') return state.remoteHead ? { stdout: `${state.remoteHead}\trefs/heads/${state.branch}\n` } : { stdout: '', code: 2 };
    if (file === 'git' && args[0] === 'push') { state.remoteHead = state.headSha; return { stdout: '' }; }
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'create') { state.rows = [row(state.intent)]; return { stdout: 'https://github.com/Acme/Project/pull/999' }; }
    throw new Error(`Unexpected command: ${key}`);
  } };
  const input = { cwd, runId: 'run-123', stageId: 'prompt', repository: 'Acme/Project', baseBranch: 'main' };
  return { cwd, calls, state, ports, input, prepare: () => prepareWorkflowPr(input, ports) };
}
const effects = calls => calls.filter(c => c.file === 'git' && c.args[0] === 'push' || c.file === 'gh' && c.args[0] === 'pr' && c.args[1] === 'create');

test('resolves same-origin issue selectors', async t => { const f = await fixture(t); assert.equal((await resolveWorkflowIssue({ cwd: f.cwd, issue: 12 }, f.ports)).issue.number, 12); });
test('prepare returns intent without body-file I/O', async t => { const f = await fixture(t), intent = await f.prepare(); assert.deepEqual(Object.keys(intent).sort(), ['baseBranch','headBranch','headSha','marker','repository','runId','stageId','title']); assert.equal(effects(f.calls).length, 0); });
test('prepare enforces clean topic and origin-independent repository safety', async t => { const f = await fixture(t); for (const [k,v] of [['dirty',' M x\\0'],['branch','main'],['count','0']]) { const old=f.state[k]; f.state[k]=v; await assert.rejects(f.prepare(), /workflow_github_/); f.state[k]=old; } });
test('prepare works through a symlink alias with arbitrary folder name', async t => { const parent=await mkdtemp(join(tmpdir(),'pdd-symlink-')); t.after(()=>rm(parent,{recursive:true,force:true})); const real=join(parent,'repo'), alias=join(parent,'run-folder-with-any-name'); await mkdir(real); await symlink(real,alias,'dir'); const f=await fixture(t); const ports={...f.ports, execFile: async (file,args,opts)=>f.ports.execFile(file,args,{...opts,cwd:f.cwd})}; const intent=await prepareWorkflowPr({cwd:alias,runId:'run-2444',stageId:'prompt',repository:'Acme/Project',baseBranch:'main'},ports); assert.equal(intent.marker,'pdd-workflow:run-2444:prompt'); });
test('publish sends body via gh stdin and preserves push/create/readback', async t => { const f=await fixture(t), intent=await f.prepare(); f.state.intent=intent; const body=`Authored\n\n<!-- ${intent.marker} -->\n`; const result=await publishWorkflowPr({cwd:f.cwd,intent,body},f.ports); assert.equal(result.state,'open'); const create=f.calls.find(c=>c.args[1]==='create'); assert.equal(create.args.at(-1),'-'); assert.equal(create.options.input,body); });
test('existing PR recovery performs no publication effects', async t => { const f=await fixture(t), intent=await f.prepare(); f.state.rows=[row(intent)]; f.calls.length=0; assert.equal((await publishWorkflowPr({cwd:f.cwd,intent,body:`<!-- ${intent.marker} -->\n`},f.ports)).state,'open'); assert.equal(effects(f.calls).length,0); });
test('marker and body length validation happen before push', async t => { const f=await fixture(t), intent=await f.prepare(); for (const body of ['no marker', 'x'.repeat(65537)+`<!-- ${intent.marker} -->`]) { f.calls.length=0; const r=await publishWorkflowPr({cwd:f.cwd,intent,body},f.ports); assert.equal(r.state,'failed'); assert.equal(effects(f.calls).length,0); } });
test('reconcile is read-only after interrupted publication', async t => { const f=await fixture(t), intent=await f.prepare(); f.state.intent=intent; f.state.intercept=true; f.ports.execFile=async (...args)=>{ if(args[1][0]==='push') throw new Error('lost'); return (await fixture(t)).ports.execFile(...args); }; const r=await reconcileWorkflowPr({cwd:f.cwd,intent},f.ports); assert.equal(r.state,'recovery_required'); });
