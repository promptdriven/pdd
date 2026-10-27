import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { readWorkflowAreas, listWorkflowAreas, formatWorkflowList } from '../src/workflow-areas.mjs';

const areas = first => ({ version: 2, areas: [{ name: first, steps: ['one'], optional: [], gate: 'approve' }, { name: 'build', steps: ['verify'], optional: [], gate: 'pr' }] });
function put(root, name, data) { mkdirSync(join(root, `pdd-${name}`), { recursive: true }); writeFileSync(join(root, `pdd-${name}`, 'workflow.json'), typeof data === 'string' ? data : JSON.stringify(data)); }

test('lookup order: project .agents, project .claude, home .agents, home .claude, then the package', t => {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-areas-'))); t.after(() => rmSync(base, { recursive: true, force: true }));
  const project = join(base, 'project'), home = join(base, 'home'), pkg = join(base, 'package'), cwd = join(project, 'src', 'deep');
  mkdirSync(cwd, { recursive: true }); mkdirSync(join(project, '.git'));
  const roots = [join(project, '.agents/skills'), join(project, '.claude/skills'), join(home, '.agents/skills'), join(home, '.claude/skills'), join(pkg, 'skills')];
  roots.forEach((root, index) => put(root, 'flow', areas(`from${index}`)));
  for (let index = 0; index < roots.length; index++) {
    const found = readWorkflowAreas({ packageRoot: pkg, name: 'flow', cwd, home });
    assert.equal(found.areas[0].name, `from${index}`); assert.equal(found.dir, join(roots[index], 'pdd-flow'));
    assert.equal(found.source, index < 2 ? 'project' : index < 4 ? 'home' : 'package');
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
