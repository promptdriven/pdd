import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {manualEffectCases} from './helpers/manual-effect-cases.mjs';
for (const [name,run] of manualEffectCases.filter(([name]) => name.startsWith('review2:'))) test(name, async t => assert.equal(await run(t),0,'held issue received an automatic effect'));

test('3129 group note stays pending when a hold arrives inside native admission', async () => {
  const {fixture,repository} = await import('./helpers/issue-sort-fixture.mjs');
  const {reconcileDependencyIntake} = await import('../src/issue-dependencies-intake.mjs');
  const {createDependencyReadPorts} = await import('../src/issue-dependencies-github.mjs');
  const w = fixture([1,2,3,4]);
  const tick = () => reconcileDependencyIntake({repository,mode:'auto'},w.ports);
  for (const number of [1,2,3]) {w.save(w.record(number));w.review(number);}
  await tick();
  const [group] = (await w.ports.sortGroups.read()).groups;
  const umbrella = w.issues.find(issue => issue.html_url === group.umbrella);
  umbrella.labels = ['pdd:working'];
  w.claims.push({issue:group.umbrella,active:true,owner:'worker'});
  w.save(w.record(4));w.review(4);
  w.ports.manualAuthority = {read:async () => ({known:true,allowed:true})};
  let held = false, posts = 0;
  const page = w.ports.github.page;
  w.ports.github.page = args => args.kind === 'timeline' && args.issue === umbrella.number
    ? {json:JSON.stringify({items:held ? [{event:'labeled',label:{name:'pdd:manual'},actor:{login:'writer'}}] : [],next:''})} : page(args);
  const native = createDependencyReadPorts({}, {
    ...w.ports, github:undefined, githubFloor:{blocked:() => false,observe:() => {}},
    admitMutation:async action => {held = true;umbrella.labels.push('pdd:manual');return action();},
    execFile:async (_file,args) => {
      const method = args[args.indexOf('--method')+1], endpoint = args.find(arg => String(arg).startsWith('repos/'));
      if (method === 'POST') {posts++;return {code:0,stdout:'{}'};}
      let value;
      if (endpoint === `repos/${repository}/issues/${umbrella.number}`) value = umbrella;
      else if (endpoint.includes('/timeline?')) value = [{event:'labeled',label:{name:'pdd:manual'},actor:{login:'writer'}}];
      else if (endpoint.includes('/comments?')) value = w.comments.get(umbrella.number);
      else assert.fail(`Unexpected native endpoint: ${endpoint}`);
      return {code:0,stdout:`HTTP/2 200 OK\r\n\r\n${JSON.stringify(value)}`,stderr:''};
    },
  });
  const append = w.ports.github.appendComment;
  w.ports.github.appendComment = native.github.appendComment;
  await tick();
  assert.equal(held,true);
  assert.equal(posts,0);
  assert.deepEqual((await w.ports.sortGroups.read()).groups[0].notified,group.notified);
  held = false;umbrella.labels = ['pdd:working'];w.ports.github.appendComment = append;
  const start = w.writes.length;
  await tick();
  assert.equal(w.writes.slice(start).filter(write => write.issue === umbrella.number).length,1);
});
