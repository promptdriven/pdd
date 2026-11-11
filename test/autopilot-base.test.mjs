import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { checkAutopilotBase } from '../src/autopilot-base.mjs';
import { githubListItems } from '../src/github-calls.mjs';
import { fixture } from './helpers/workflow-runner-fixture.mjs';

const capture = () => ({ text: '', write(value) { this.text += value; } });
async function baseWorld(t, changes = {}) {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.baseBranch = 'integration/topic';
  run.pr = [{ number: 23, url: 'https://github.com/example/project/pull/23', base: run.baseBranch, stage: 'change' }];
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
  const calls = [], world = {
    pull: { number:23, state:'open', base:{ref:run.baseBranch, repo:{full_name:run.repo}} },
    metadata: {default_branch:'trunk'},
    releases: [[{draft:false,tag_name:'v1.0',published_at:'2026-01-01T00:00:00Z'}], [
      {draft:true,tag_name:'v3',published_at:null},
      {draft:false,prerelease:true,tag_name:'alpha-v2',published_at:'2026-02-01T00:00:00Z'}]],
    defaultCompare: {behind_by:0,status:'ahead'}, releaseCompare:{behind_by:0,status:'ahead'},
    ...changes,
  };
  const execute = async (file,args,opts) => {
    if(file!=='gh') return f.ports.execFile(file,args,opts);
    calls.push(args);
    assert.equal(args[0],'api');
    assert.equal(args.some(a=>['POST','PATCH','PUT','DELETE'].includes(a)),false);
    const path=args[1]; let value;
    if (world.failure && path.includes(world.failure)) throw Error('synthetic unavailable read');
    if(path===`repos/${run.repo}/pulls/23`)value=world.pull;
    else if(path===`repos/${run.repo}`)value=world.metadata;
    else if(path===`repos/${run.repo}/releases?per_page=100`) {
      // gh 2.45 (Ubuntu) has no --slurp; every page comes as one release per line with --paginate --jq.
      if(args.includes('--slurp')) return {code:1,stdout:'',stderr:'unknown flag: --slurp\n\nUsage:  gh api <endpoint> [flags]'};
      assert.ok(args.includes('--paginate'));assert.match(args[args.indexOf('--jq')+1],/^\.\[\] \| \{tag_name, draft, published_at\} \| tojson$/);
      return {code:0,stdout:world.releases.flat().map(r=>JSON.stringify({tag_name:r.tag_name,draft:r.draft,published_at:r.published_at})+'\n').join(''),stderr:''};
    }
    else if(path.includes('/compare/trunk...'))value=world.defaultCompare;
    else if(path.includes('/compare/alpha-v2...'))value=world.releaseCompare;
    else assert.fail(`Unexpected fake read: ${path}`);
    return {code:0,stdout:JSON.stringify(value),stderr:''};
  };
  // The merge guard that the core engine calls (checkAutopilotBase) with the saved run, through the same fake reads.
  f.check = async (pr='23') => {
    const out=await checkAutopilotBase({run:f.record(),pr},{execFile:async(file,args,opts)=>{const result=await execute(file,args,opts);return {code:result.code ?? 0,stdout:result.stdout ?? '',stderr:result.stderr ?? ''};}});
    return {code:out.exitCode,text:out.message,stdout:out.exitCode===0?out.message:'',stderr:out.exitCode===0?'':out.message};
  };
  return {...f,world,calls,run};
}

test('3071 merge guard accepts the saved target and newest published prerelease',async t=>{
  const f=await baseWorld(t),out=await f.check();
  assert.equal(out.code,0,out.text);assert.equal(out.stderr,'');
  assert.ok(out.text.includes('integration/topic'));assert.ok(out.text.includes('alpha-v2'));
  assert.equal(f.calls.length,5);
  assert.ok(f.calls.some(args=>args[1].endsWith('alpha-v2...integration%2Ftopic')));
});
for (const [name,changes,reason] of [
  ['wrong target',{pull:{number:23,base:{ref:'alpha',repo:{full_name:'example/project'}}}},'integration/topic'],
  ['behind default',{defaultCompare:{behind_by:431,status:'behind'}},'trunk'],
  ['diverged default',{defaultCompare:{behind_by:1,status:'diverged'}},'trunk'],
  ['missing release',{releaseCompare:{behind_by:1,status:'diverged'}},'alpha-v2'],
  ['unknown ancestry',{defaultCompare:{}},'ancestry'],
  ['release read failure',{failure:'/releases?'},'releases'],
  ['unknown default',{metadata:{}},'default'],
  ['malformed releases',{releases:[[{draft:false,tag_name:'v3',published_at:null}]]},'release'],
  ['foreign target',{pull:{number:23,base:{ref:'integration/topic',repo:{full_name:'other/project'}}}},'target'],
]) test(`3071 merge guard refuses ${name}`,async t=>{
  const f=await baseWorld(t,changes),out=await f.check();
  assert.equal(out.code,1,out.text);assert.equal(out.stdout,'');assert.ok(out.text.includes(reason));
});
test('3071 no releases still checks default ancestry',async t=>{
  const f=await baseWorld(t,{releases:[[]]}),out=await f.check();assert.equal(out.code,0,out.text);assert.equal(f.calls.length,4);
});
test('3071 post-merge audit reads actual base again and detects wrong target',async t=>{
  const f=await baseWorld(t); assert.equal((await f.check()).code,0);
  f.world.pull.state='closed'; f.world.pull.merged=true; f.world.pull.base.ref='alpha';
  const out=await f.check();assert.equal(out.code,1,out.text);assert.ok(out.text.includes('alpha'));assert.equal(f.calls.length,6);
});
test('3071 safety reads do not reuse an earlier ancestry result',async t=>{
  const f=await baseWorld(t); assert.equal((await f.check()).code,0);
  f.world.defaultCompare={behind_by:1,status:'behind'};
  const out=await f.check();assert.equal(out.code,1,out.text);assert.ok(out.text.includes('trunk'));assert.equal(f.calls.length,9);
});
test('3071 unknown PR refuses before GitHub reads',async t=>{
  const f=await baseWorld(t),out=await f.check('99');assert.equal(out.code,1);assert.equal(f.calls.length,0);
});

// The core's counted gh port returns {code, stdout, stderr}. It models gh 2.45: no --slurp; --paginate --jq prints
// one result per line for every page.
const corePort = ({ pages, releaseError } = {}) => {
  const calls = [];
  const execFile = async (file, args) => {
    calls.push(args);
    assert.equal(file, 'gh');
    if (args.includes('--slurp')) return { code: 1, stdout: '', stderr: 'unknown flag: --slurp\n\nUsage:  gh api <endpoint> [flags]\n' };
    const path = args[1];
    const json = value => ({ code: 0, stdout: JSON.stringify(value), stderr: '' });
    if (path === 'repos/acme/pdd/pulls/7') return json({ number: 7, base: { ref: 'main', repo: { full_name: 'acme/pdd' } } });
    if (path === 'repos/acme/pdd') return json({ default_branch: 'main' });
    if (path === 'repos/acme/pdd/releases?per_page=100') {
      if (releaseError) return { code: 1, stdout: '', stderr: releaseError };
      assert.deepEqual(args.slice(2), ['--paginate', '--jq', '.[] | {tag_name, draft, published_at} | tojson']);
      return { code: 0, stdout: pages.flat().map(r => `${JSON.stringify({ tag_name: r.tag_name, draft: r.draft, published_at: r.published_at })}\n`).join(''), stderr: '' };
    }
    if (path.includes('/compare/')) return json({ behind_by: 0, status: 'ahead' });
    assert.fail(`Unexpected read: ${path}`);
  };
  return { calls, execFile };
};
const coreRun = { repo: 'acme/pdd', baseBranch: 'main', root: '/nowhere', pr: [{ number: 7 }] };

test('#3197 the base check reads every release page on gh 2.45 (no --slurp): 3 pages, the newest release on the last page', async () => {
  const release = (n, day) => ({ tag_name: `v0.1.${n}`, draft: false, prerelease: false, published_at: `2026-${String(1 + Math.floor(day / 28)).padStart(2, '0')}-${String(1 + day % 28).padStart(2, '0')}T00:00:00Z`, body: 'x'.repeat(2000) });
  const pages = [Array.from({ length: 100 }, (_, i) => release(i, i)), Array.from({ length: 100 }, (_, i) => release(100 + i, i)), [release(300, 250), { tag_name: 'v9', draft: true, published_at: null }]];
  const port = corePort({ pages });
  const out = await checkAutopilotBase({ run: coreRun, pr: '7' }, { execFile: port.execFile });
  assert.equal(out.exitCode, 0, out.message);
  assert.match(out.message, /newest release tag v0\.1\.300/);
  assert.equal(port.calls.some(args => args.includes('--slurp')), false);
  assert.ok(port.calls.some(args => args[1].endsWith('/compare/v0.1.300...main')));
});

test('#3197 a failed release read names its real cause, and the core still reads it as a retry', async () => {
  const out = await checkAutopilotBase({ run: coreRun, pr: '7' }, { execFile: corePort({ releaseError: 'HTTP 502: Bad Gateway (https://api.github.com/repos/acme/pdd/releases?per_page=100)\n' }).execFile });
  assert.equal(out.exitCode, 1);
  assert.equal(out.message, 'Automatic merge refused: main: could not verify releases (HTTP 502: Bad Gateway (https://api.github.com/repos/acme/pdd/releases?per_page=100)); retry the read before merging.');
  assert.match(out.message, /could not verify/, 'the core retries this text');
  const thrown = await checkAutopilotBase({ run: coreRun, pr: '7' }, { execFile: async (file, args) => { if (args[1].includes('/releases')) throw Object.assign(Error('Command failed'), { stderr: 'unknown flag: --jq\n' }); return corePort({ pages: [[]] }).execFile(file, args); } });
  assert.match(thrown.message, /could not verify releases \(unknown flag: --jq\)/);
});

test('githubListItems reads one JSON item per line and the items of a whole JSON list', () => {
  assert.deepEqual(githubListItems('{"a":1}\n{"a":"x\\ny"}\n\n'), [{ a: 1 }, { a: 'x\ny' }]);
  assert.deepEqual(githubListItems('[{"a":1},{"a":2}]\n[{"a":3}]'), [{ a: 1 }, { a: 2 }, { a: 3 }]);
  assert.deepEqual(githubListItems(''), []);
  assert.throws(() => githubListItems('{"a":'));
});
