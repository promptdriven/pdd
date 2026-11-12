import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, mkdirSync, symlinkSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { runPdd } from '../src/pdd-cli.mjs';
import { interfaceBlocks, proseSha256 } from '../src/runtime-preflight.mjs';
import { harbor, PLACE, sink } from './runtime-fake.mjs';

const draft = async (setup,args) => {
  const stdout=sink(),stderr=sink();
  const code=await runPdd(['interface','draft',...args],{cwd:setup.repo,stdout,stderr,env:{HOME:setup.home},pathDiagnostic:()=>[]});
  return {code,out:stdout.text,err:stderr.text};
};
export function explicitContract(repo) {
  const file=join(repo,PLACE),text=readFileSync(file,'utf8'),block=interfaceBlocks(text)[0],iface=JSON.parse(block[1]);
  delete iface.status;delete iface.prose_sha256;
  const prose=text.replace(block[0],'')+'\n## Public schema\n\n```json\n'+JSON.stringify(iface)+'\n```\n';
  writeFileSync(file,prose);
  return prose;
}

test('draft from an explicit contract preserves prose, fills a current hash and stays draft', async t => {
  let before;
  const setup=harbor(t,repo=>{before=explicitContract(repo);});
  const result=await draft(setup,[PLACE,'--json']);
  assert.equal(result.code,0,result.err);
  const summary=JSON.parse(result.out);
  assert.deepEqual(summary.summary,{drafted:1,existing:0,lint_clean:1,refused:0,total:1});
  const next=readFileSync(join(setup.repo,PLACE),'utf8'),block=interfaceBlocks(next)[0],iface=JSON.parse(block[1]);
  assert.equal(next.replace(block[0],''),before);
  assert.equal(iface.status,'draft');assert.equal(Object.hasOwn(iface,'kind'),false,'full drafts use the Runtime-admitted implicit full spelling');
  assert.equal(iface.prose_sha256,proseSha256(next));
  assert.equal(iface.entries[0].operation,'place_order');
  assert.equal(iface.entries[0].input_schema.properties.customerName.type,'string');
  const second=await draft(setup,[PLACE,'--json']);
  assert.equal(second.code,0);assert.equal(JSON.parse(second.out).summary.existing,1);
  assert.equal(readFileSync(join(setup.repo,PLACE),'utf8'),next);
  assert.ok(readFileSync(join(setup.repo,'.pdd/interface-drafts.json'),'utf8').includes(PLACE));
});

test('bulk draft keeps uncertain exports as gaps and reports each prompt independently', async t => {
  const setup=harbor(t,repo=>{
    explicitContract(repo);
    mkdirSync(join(repo,'src'),{recursive:true});
    writeFileSync(join(repo,'src/mystery.mjs'),'export function mystery(value) { return value; }\n');
    writeFileSync(join(repo,'prompts/mystery.prompt.md'),'# Mystery\n\nOwn `src/mystery.mjs`. Return the caller value.\n');
  });
  const result=await draft(setup,['--all','--json']);
  assert.equal(result.code,4,result.err);
  const report=JSON.parse(result.out);
  assert.deepEqual(report.summary,{drafted:2,existing:0,lint_clean:1,refused:1,total:2});
  const gap=report.rows.find(row=>row.path.includes('mystery'));
  assert.ok(gap.problems.some(problem=>problem.code==='interface-draft-incomplete'));
  const iface=JSON.parse(interfaceBlocks(readFileSync(join(setup.repo,gap.path),'utf8'))[0][1]);
  assert.equal(iface.kind,'partial');assert.equal(iface.entries[0].operation,'mystery');
  assert.equal(Object.hasOwn(iface.entries[0],'input_schema'),false);
  for(const field of ['calls','resources','limits']) assert.equal(Object.hasOwn(iface,field),false);
});

test('draft reads declared shared contracts and expands schema references for lint', async t => {
  const setup=harbor(t,repo=>{
    const file=join(repo,PLACE),text=readFileSync(file,'utf8'),block=interfaceBlocks(text)[0],iface=JSON.parse(block[1]);
    mkdirSync(join(repo,'contracts'),{recursive:true});
    writeFileSync(join(repo,'contracts/shapes.json'),JSON.stringify({order:iface.entries[0].input_schema}));
    iface.entries[0].input_schema={$contract:'contracts/shapes.json#/order'};
    writeFileSync(join(repo,'contracts/interface.json'),JSON.stringify(iface));
    writeFileSync(file,text.replace(block[0],'').replace('## Dependencies','## Dependencies\n\n- [Interface](../contracts/interface.json): required contract context.\n- [Shapes](../contracts/shapes.json): required schema context.'));
  });
  // Harbor's prompt is one directory deep, so dependency paths are relative to it.
  const file=join(setup.repo,PLACE);
  writeFileSync(file,readFileSync(file,'utf8').replaceAll('../../contracts/','../contracts/'));
  const result=await draft(setup,[PLACE,'--json']);
  assert.equal(result.code,0,result.err+result.out);
  assert.equal(JSON.parse(result.out).summary.lint_clean,1);
});

test('draft validates the whole explicit selection before writing and rejects links', async t => {
  const setup=harbor(t,repo=>explicitContract(repo));
  assert.equal((await draft(setup,[PLACE,'--json'])).code,0);
  const before=readFileSync(join(setup.repo,PLACE),'utf8');
  const invalid=await draft(setup,[PLACE,'../outside.prompt.md']);
  assert.equal(invalid.code,2);assert.equal(readFileSync(join(setup.repo,PLACE),'utf8'),before);
  const conflict=await draft(setup,[PLACE,'--all']);assert.equal(conflict.code,2);
  symlinkSync(join(setup.repo,PLACE),join(setup.repo,'prompts/link.prompt.md'));
  assert.equal((await draft(setup,['prompts/link.prompt.md'])).code,2);
});

test('bulk draft respects the workspace and does not draft nested fixture projects', async t => {
  const setup=harbor(t,repo=>{
    explicitContract(repo);
    mkdirSync(join(repo,'test/fixtures/nested/prompts'),{recursive:true});
    mkdirSync(join(repo,'test/fixtures/nested/user_stories'),{recursive:true});
    mkdirSync(join(repo,'test/fixtures/nested/tests'),{recursive:true});
    writeFileSync(join(repo,'test/fixtures/nested/prompts/n.prompt.md'),'# Fixture only\n');
    writeFileSync(join(repo,'test/fixtures/nested/user_stories/n.md'),'# N\n');
    writeFileSync(join(repo,'test/fixtures/nested/tests/n.json'),'{}');
    writeFileSync(join(repo,'prompts/excluded.prompt.md'),'# Outside workspace\n');
    writeFileSync(join(repo,'pdd-workspace.json'),JSON.stringify({allowed_paths:[PLACE,'user_stories/','tests/','test/fixtures/']}));
  });
  const result=await draft(setup,['--all','--json']);
  assert.equal(result.code,0,result.out+result.err);
  assert.equal(JSON.parse(result.out).summary.total,1);
  assert.equal(interfaceBlocks(readFileSync(join(setup.repo,'test/fixtures/nested/prompts/n.prompt.md'),'utf8')).length,0);
  assert.equal(interfaceBlocks(readFileSync(join(setup.repo,'prompts/excluded.prompt.md'),'utf8')).length,0);
});

test('setup offers offline drafts, respects a decline, and does not approve an accepted draft', async t => {
  for(const answer of ['n','y',null]) {
    const setup=harbor(t,repo=>explicitContract(repo));
    const stdout={...sink(),isTTY:answer!==null},stderr=sink(),questions=[];
    const code=await runPdd(['setup'],{cwd:setup.repo,stdout,stderr,stdin:{isTTY:answer!==null},env:{HOME:setup.home},
      pathDiagnostic:()=>[],setupSkills:()=>[],setupProject:()=>({file:'AGENTS.md',changed:false}),setupAgentMcp:async()=>0,
      workflowAgents:{checkWorkflowAgents:async()=>({ok:true,agent:'codex'})},gitContext:async()=>({toplevel:setup.repo}),
      autopilot:{runAutopilot:async()=>({exitCode:0,message:''})},
      ...(answer===null ? {} : {confirm:async question=>{questions.push(question);return answer;}})});
    assert.equal(code,0,stderr.text);
    assert.match(stdout.text,/pdd interface draft --all/);
    assert.equal(questions.length,answer===null ? 0 : 1);
    const blocks=interfaceBlocks(readFileSync(join(setup.repo,PLACE),'utf8'));
    assert.equal(blocks.length,answer==='y' ? 1 : 0);
    if(blocks.length) assert.equal(JSON.parse(blocks[0][1]).status,'draft');
  }
});


test('draft leaves missing execution limits as a visible gap instead of inventing them', async t => {
  const setup=harbor(t,repo=>{
    explicitContract(repo);
    const file=join(repo,PLACE),text=readFileSync(file,'utf8');
    const match=[...text.matchAll(/```json\n([\s\S]*?)\n```/g)].at(-1),contract=JSON.parse(match[1]);
    delete contract.limits;
    writeFileSync(file,text.replace(match[1],JSON.stringify(contract)));
  });
  const result=await draft(setup,[PLACE,'--json']);
  assert.equal(result.code,4,result.err+result.out);
  const row=JSON.parse(result.out).rows[0];
  assert.equal(row.lint_clean,false);
  assert.ok(row.problems.some(problem=>problem.code==='interface-draft-incomplete'));
  const iface=JSON.parse(interfaceBlocks(readFileSync(join(setup.repo,PLACE),'utf8'))[0][1]);
  assert.equal(iface.kind,'partial');assert.equal(Object.hasOwn(iface,'limits'),false);
});
