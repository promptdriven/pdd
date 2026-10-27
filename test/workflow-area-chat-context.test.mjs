import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { loadAreaChatPrompts, buildAreaChatPrompt, buildAreaStageTask } from '../src/workflow-area-chat-context.mjs';

const prompts = loadAreaChatPrompts();
const input = { area: 'plan', agent: 'codex', issueNumber: 45, runId: 'saved-run',
  context: 'Complete saved guide and workflow context. {{scopeCommand}} is literal here.', prompts };

test('shipped templates cover the actual small-change definition and preserve saved inputs', () => {
  const definition = JSON.parse(readFileSync(new URL('../.pdd/workflows/small-change/workflow.json', import.meta.url)));
  for (const { id } of definition.stages) {
    const instructions = `Exact ${id} packet with a literal {{changeCommand}} and JSON handoff identity.`;
    const task = buildAreaStageTask({ stageId: id, instructions, prompts });
    if (['scope', 'change', 'verify'].includes(id)) assert.ok(task.includes(`pdd step done ${id}`));
    else assert.ok(!task.includes(`pdd step done ${id}`));
    assert.ok(task.endsWith(instructions));
  }
  const rendered = buildAreaChatPrompt(input);
  assert.ok(rendered.startsWith(input.context));
  assert.ok(rendered.includes('Chat 1: plan'));
  assert.ok(rendered.includes('pdd workflow approve 45'));
  assert.ok(rendered.includes('pdd step done scope'));
  assert.ok(!rendered.includes('pdd step done change'));
});

test('build uses the saved prompt snapshot and emits the ordered current-stage reports', () => {
  const snapshot = structuredClone(prompts);
  snapshot.build += '\nSaved run template revision.';
  for (const agent of ['codex', 'claude']) {
    const rendered = buildAreaChatPrompt({ ...input, area: 'build', agent, prompts: snapshot });
    assert.ok(rendered.includes('Chat 2: build'));
    const reports = [...rendered.matchAll(/pdd step done ([\w-]+)/g)].map(match => match[1]);
    assert.deepEqual(reports, ['change', 'verify']);
    assert.ok(rendered.includes(agent === 'codex' ? 'Codex native multi_agent' : 'Claude native subagents'));
    assert.ok(rendered.endsWith('Saved run template revision.'));
  }
  assert.ok(!loadAreaChatPrompts().build.includes('Saved run template revision.'));
});

test('an actual shell preserves executable argv containing spaces, apostrophes and shell syntax', () => {
  // printf stands in only for inspecting shell argv, not for PDD or model acceptance.
  const argv = ['printf', '%s\\n', "/tmp/pdd's path/$(false);`false`"];
  const task = buildAreaStageTask({ stageId: 'scope', instructions: 'Exact request.', prompts, pddCommand: argv });
  const command = task.match(/main chat reports with (.+); do not run/)[1];
  assert.equal(execFileSync('/bin/sh', ['-c', command], { encoding: 'utf8' }),
    "/tmp/pdd's path/$(false);`false`\nstep\ndone\nscope\n");
});

test('invalid requests never produce an actionable default chat or task', () => {
  for (const [field, value] of [['area', 'unknown'], ['agent', 'unknown'], ['issueNumber', 0],
    ['issueNumber', '45'], ['runId', ''], ['context', ''], ['prompts', {}],
    ['pddCommand', []], ['pddCommand', ['pdd\nfalse']], ['pddCommand', 'pdd']]) {
    assert.throws(() => buildAreaChatPrompt({ ...input, [field]: value }), new RegExp(field));
  }
  assert.throws(() => buildAreaStageTask({ stageId: 'approve-plan', instructions: 'x', prompts }), /stageId/);
  assert.throws(() => buildAreaStageTask({ stageId: 'scope', instructions: '', prompts }), /instructions/);
});

test('runner integration retains exact attempt command and returned next-stage protocol', async () => {
  const { buildAreaChatInstructions } = await import('../src/workflow-area-chat-context.mjs');
  const reportCommand = "'/actual package/node' '/actual package/pdd.mjs' step done scope saved original";
  const approvalCommand = "'/actual package/node' '/actual package/pdd.mjs' workflow approve 45";
  const stageInstructions = 'PDD_STAGE_INPUT_JSON\n{"stageId":"scope","attemptId":"original"}\nPDD_STAGE_INPUT_END';
  const args = { area: { id: 'plan', label: 'Chat 1: plan', gate: 'approve-plan' },
    stageInstructions, reportCommand, approvalCommand, changesText: null, prompts };
  const output = buildAreaChatInstructions(args);
  assert.ok(output.includes(reportCommand));
  assert.ok(output.includes(approvalCommand));
  assert.ok(output.includes('nextStageInstructions'));
  assert.ok(output.endsWith(stageInstructions));
  assert.ok(!output.includes('pdd step done scope'));
  assert.throws(() => buildAreaChatInstructions({ ...args, area: { ...args.area, gate: 'merge' } }), /area/);
  assert.throws(() => buildAreaChatInstructions({ ...args, reportCommand: 'pdd\nfalse' }), /reportCommand/);
});
