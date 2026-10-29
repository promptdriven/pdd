import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { readWorkflowAreas, listWorkflowAreas, formatWorkflowList } from '../src/workflow-areas.mjs';

const areas = first => ({ version: 2, areas: [{ name: first, steps: ['one'], optional: [], gate: 'approve' }, { name: 'build', steps: ['verify'], optional: [], gate: 'pr' }] });
function put(root, name, data) { mkdirSync(join(root, `pdd-${name}`), { recursive: true }); writeFileSync(join(root, `pdd-${name}`, 'workflow.json'), typeof data === 'string' ? data : JSON.stringify(data)); }

test('lookup order: project .agents, project .claude, home .agents, home .claude, then the package; home never shadows a package workflow', t => {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-areas-'))); t.after(() => rmSync(base, { recursive: true, force: true }));
  const project = join(base, 'project'), home = join(base, 'home'), pkg = join(base, 'package'), cwd = join(project, 'src', 'deep');
  mkdirSync(cwd, { recursive: true }); mkdirSync(join(project, '.git'));
  const roots = [join(project, '.agents/skills'), join(project, '.claude/skills'), join(home, '.agents/skills'), join(home, '.claude/skills'), join(pkg, 'skills')];
  roots.forEach((root, index) => put(root, 'flow', areas(`from${index}`)));
  // A home copy of a workflow the package has is an install (npx skills add or pdd setup), maybe an old one: the package wins.
  for (const index of [0, 1, 4]) {
    const found = readWorkflowAreas({ packageRoot: pkg, name: 'flow', cwd, home });
    assert.equal(found.areas[0].name, `from${index}`); assert.equal(found.dir, join(roots[index], 'pdd-flow'));
    assert.equal(found.source, index < 2 ? 'project' : 'package');
    rmSync(join(roots[index], 'pdd-flow'), { recursive: true });
  }
  // A workflow only in a home folder (a person's own) comes from home: .agents before .claude.
  for (const index of [2, 3]) {
    const found = readWorkflowAreas({ packageRoot: pkg, name: 'flow', cwd, home });
    assert.equal(found.areas[0].name, `from${index}`); assert.equal(found.source, 'home');
    rmSync(join(roots[index], 'pdd-flow'), { recursive: true });
  }
  put(join(pkg, 'skills'), 'small-change', areas('plan')); put(join(home, '.claude/skills'), 'docs', areas('draft'));
  mkdirSync(join(home, '.agents/skills/pdd-prompting'), { recursive: true });
  const listed = listWorkflowAreas({ packageRoot: pkg, cwd, home });
  assert.deepEqual(listed.map(item => [item.name, item.source]), [['docs', 'home'], ['small-change', 'package']]);
  assert.match(formatWorkflowList(listed), /docs {2}draft \[one\] → approve → build \[verify\] → pr {2}\(home\)/);
  assert.throws(() => readWorkflowAreas({ packageRoot: pkg, name: 'nope', cwd, home }), /Workflows: docs, small-change/);
  put(join(project, '.agents/skills'), 'docs', '{"version":2,"areas":[{"name":"x","steps":["a"],"gate":"approve"}]}');
  assert.throws(() => readWorkflowAreas({ packageRoot: pkg, name: 'docs', cwd, home }), error => error.code === 'workflow_invalid' && error.message.includes(join(project, '.agents/skills/pdd-docs/workflow.json')));
});

test('a pr gate before the last area needs then ask-code; the last area needs a plain pr gate', t => {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-areas-'))); t.after(() => rmSync(base, { recursive: true, force: true }));
  const pkg = join(base, 'package'), skills = join(pkg, 'skills');
  const three = (middle, last = { name: 'code', steps: ['build', 'verify'], optional: [], gate: 'pr' }) => ({ version: 2, areas: [
    { name: 'story', steps: ['prompt-story'], optional: [], gate: 'approve' }, { name: 'prompt-pr', steps: ['check', 'try'], optional: ['try'], ...middle }, last] });
  put(skills, 'feature', three({ gate: 'pr', then: 'ask-code' }));
  assert.deepEqual(readWorkflowAreas({ packageRoot: pkg, name: 'feature', home: base }).areas.map(area => [area.name, area.gate, area.then ?? null]),
    [['story', 'approve', null], ['prompt-pr', 'pr', 'ask-code'], ['code', 'pr', null]]);
  for (const [middle, last] of [[{ gate: 'pr' }], [{ gate: 'approve', then: 'ask-code' }], [{ gate: 'pr', then: 'ask-code' }, { name: 'code', steps: ['build'], optional: [], gate: 'pr', then: 'ask-code' }]]) {
    put(skills, 'feature', three(middle, last));
    assert.throws(() => readWorkflowAreas({ packageRoot: pkg, name: 'feature', home: base }), error => error.code === 'workflow_invalid');
  }
});

test('an installed home copy (with or without pdd\'s marker) never shadows the running package', t => {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-areas-'))); t.after(() => rmSync(base, { recursive: true, force: true }));
  const home = join(base, 'home'), pkg = join(base, 'package');
  put(join(pkg, 'skills'), 'bug', areas('new'));
  put(join(home, '.agents/skills'), 'bug', areas('stale'));
  writeFileSync(join(home, '.agents/skills/pdd-bug/.pdd-skill.json'), JSON.stringify({ package: 'pdd', version: '0.1.2', digest: 'x' }));
  const found = readWorkflowAreas({ packageRoot: pkg, name: 'bug', home });
  assert.equal(found.areas[0].name, 'new'); assert.equal(found.source, 'package'); assert.equal(found.dir, join(pkg, 'skills/pdd-bug'));
  rmSync(join(home, '.agents/skills/pdd-bug/.pdd-skill.json'));
  assert.equal(readWorkflowAreas({ packageRoot: pkg, name: 'bug', home }).areas[0].name, 'new', 'npx skills add copies have no marker; they still lose to the package');
});

test('#13: "before":"approve" is allowed only on a pr gate', t => {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-areas-'))); t.after(() => rmSync(base, { recursive: true, force: true }));
  const pkg = join(base, 'package'), skills = join(pkg, 'skills');
  const shape = (middle, last = {}) => ({ version: 2, areas: [{ name: 'story', steps: ['a'], optional: [], gate: 'approve', ...middle.story },
    { name: 'prompt-pr', steps: ['check'], optional: [], gate: 'pr', then: 'ask-code', ...middle.pr }, { name: 'code', steps: ['build'], optional: [], gate: 'pr', ...last }] });
  put(skills, 'feature', shape({ pr: { before: 'approve' } }, { before: 'approve' }));
  assert.deepEqual(readWorkflowAreas({ packageRoot: pkg, name: 'feature', home: base }).areas.map(area => area.before ?? null), [null, 'approve', 'approve']);
  assert.match(formatWorkflowList(listWorkflowAreas({ packageRoot: pkg, home: base })), /prompt-pr \[check\] → approve → pr → code \[build\] → approve → pr/);
  for (const bad of [shape({ story: { before: 'approve' } }), shape({ pr: { before: 'yes' } })]) {
    put(skills, 'feature', bad);
    assert.throws(() => readWorkflowAreas({ packageRoot: pkg, name: 'feature', home: base }), error => error.code === 'workflow_invalid');
  }
});

test('2530: replay policy is explicit, retained, versioned and limited to pr gates',t=>{
  const base=realpathSync(mkdtempSync(join(tmpdir(),'pdd-areas-')));t.after(()=>rmSync(base,{recursive:true,force:true}));
  const pkg=join(base,'pkg'),skills=join(pkg,'skills'),data=areas('plan');
  put(skills,'custom',data);assert.equal(readWorkflowAreas({packageRoot:pkg,name:'custom',home:base}).areas[1].replay_evidence,undefined);
  data.areas[1].replay_evidence='pdd.replay-evidence.v1';put(skills,'custom',data);
  assert.equal(readWorkflowAreas({packageRoot:pkg,name:'custom',home:base}).areas[1].replay_evidence,'pdd.replay-evidence.v1');
  for(const bad of ['pdd.replay-evidence.v2',true]){data.areas[1].replay_evidence=bad;put(skills,'custom',data);assert.throws(()=>readWorkflowAreas({packageRoot:pkg,name:'custom',home:base}),/replay-evidence/);}
  delete data.areas[1].replay_evidence;data.areas[0].replay_evidence='pdd.replay-evidence.v1';put(skills,'custom',data);assert.throws(()=>readWorkflowAreas({packageRoot:pkg,name:'custom',home:base}),/replay-evidence/);
});
