import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { renderHelp } from '../src/pdd-cli.mjs';
import * as runner from '../src/workflow-runner.mjs';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';

const pointer = (value, path) => path === '' ? value : path.slice(1).split('/').reduce((v, k) => v?.[k.replace(/~1/g, '/').replace(/~0/g, '~')], value);

test('workflow-answer: replay all frozen scenario checks', async () => {
  assert.equal(typeof runner.answerRun, 'function', 'answerRun is exported from workflow-runner');
  assert.equal(typeof runner.changeRun, 'function', 'changeRun is exported from workflow-runner');
  const scenario = JSON.parse(readFileSync(new URL('./runtime/workflow-answer.json', import.meta.url), 'utf8'));
  const world = structuredClone(scenario.initial_world);
  for (const step of scenario.steps) {
    const calls = { resources: {} };
    const count = id => { calls.resources[id] = (calls.resources[id] ?? 0) + 1; };
    const ports = {
      runs: {
        load: async ({ ref }) => {
          count('workflow-runner-runs-load');
          return { run: structuredClone(world.runs[ref] ?? null) };
        },
        save: async ({ ref, run }) => {
          count('workflow-runner-runs-save');
          world.runs[ref] = structuredClone(run);
          return { saved: true };
        }
      },
      chat: {
        send: async input => {
          count('workflow-runner-chat-send');
          world.chat_messages.push(structuredClone(input));
          return { ok: true };
        }
      }
    };
    const fn = runner[step.operation];
    assert.equal(typeof fn, 'function', `${step.step_id}: missing operation ${step.operation}`);
    const result = await fn(structuredClone(step.input), ports);
    for (const check of step.checks) {
      const actual = pointer({ result, world, calls }[check.target], check.path);
      const got = check.target === 'calls' && actual === undefined ? 0 : actual;
      assert.equal(check.op, 'equals');
      assert.deepEqual(got, check.value, `${step.step_id} ${check.target}${check.path}`);
    }
  }
});

test('workflow-answer: CLI help, dispatch and native runner cover AC1, AC2, AC3 and edge cases', async t => {
  assert.match(renderHelp(['workflow', 'answer']), /pdd workflow answer ISSUE TEXT\s+Send an answer to the area chat that waits for one\./);
  assert.equal(typeof runner.answerRun, 'function', 'answerRun is exported from workflow-runner');

  const f = await fixture(t, { agent: 'codex', name: 'feature' });
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), pane = f.herdr.paneOf(run.chats[0]);
  f.tick();

  // Ask a question in the story chat; hint teaches pdd workflow answer.
  const asked = await runner.askPerson({ text: 'Which date format?', cwd: run.root }, f.agentPorts());
  assert.equal(asked.exitCode, 0, asked.message);
  assert.match(asked.message, /pdd workflow answer 17 "answer"/);
  assert.equal(f.record().question.text, 'Which date format?');
  assert.equal(f.record().state, 'waiting');

  // Empty answer is refused before touching the run log or chat.
  f.tick();
  const empty = await runner.answerRun({ ref: '17', text: '   ', cwd: f.source }, f.ports);
  assert.equal(empty.exitCode, 1);
  assert.equal(empty.message, 'Write the answer after the issue number.');
  assert.equal(f.record().changes.length, 0);

  // AC1: pdd workflow answer sends the answer, records round 1 with answer: true, clears question and sets state to running.
  const callCli = async argv => {
    let stdout = '', stderr = '';
    const exitCode = await runPdd(argv, {
      cwd: f.source,
      stdout: { write: s => { stdout += s; } },
      stderr: { write: s => { stderr += s; } },
      workflowRunner: {
        answerRun: input => runner.answerRun(input, f.ports),
        changeRun: input => runner.changeRun(input, f.ports)
      }
    });
    return { exitCode, stdout, stderr };
  };

  f.tick();
  const ac1 = await callCli(['workflow', 'answer', '17', 'ISO']);
  assert.equal(ac1.exitCode, 0, ac1.stderr);
  assert.equal(ac1.stdout.trim(), 'Sent your answer to the story chat of #17. The agent goes on with the step.');
  assert.equal(pane.agent.prompts.at(-1), 'The person answers your question: ISO Go on with the step.');
  let saved = f.record();
  assert.equal(saved.question, null);
  assert.equal(saved.state, 'running');
  assert.equal(saved.changes.length, 1);
  assert.equal(saved.changes[0].stage, 'story');
  assert.equal(saved.changes[0].round, 1);
  assert.equal(saved.changes[0].text, 'ISO');
  assert.equal(saved.changes[0].answer, true);

  // AC2: When no question is open, pdd workflow answer refuses with exitCode 1, sends 0 chat messages and saves nothing.
  const promptsBefore = pane.agent.prompts.length;
  const journalPath = join(run.runDir, 'delivery-journal.json');
  const journalBefore = readFileSync(journalPath, 'utf8');
  f.tick();
  const ac2 = await callCli(['workflow', 'answer', '17', 'ISO']);
  assert.equal(ac2.exitCode, 1);
  assert.equal(ac2.stderr.trim(), 'No question is open for example/project#17.');
  assert.equal(pane.agent.prompts.length, promptsBefore);
  assert.equal(readFileSync(journalPath, 'utf8'), journalBefore);
  assert.equal(f.record().changes.length, 1);

  // AC3: With no open question left, pdd workflow changes saves round 2 with no answer flag.
  f.tick();
  const ac3 = await callCli(['workflow', 'changes', '17', 'Use ISO dates']);
  assert.equal(ac3.exitCode, 0, ac3.stderr);
  saved = f.record();
  assert.equal(saved.changes.length, 2);
  assert.equal(saved.changes[1].stage, 'story');
  assert.equal(saved.changes[1].round, 2);
  assert.equal(saved.changes[1].text, 'Use ISO dates');
  assert.equal(Object.hasOwn(saved.changes[1], 'answer'), false);

  // A question from a different area is not considered open for answerRun.
  const withForeignQuestion = f.record();
  withForeignQuestion.question = { text: 'Question from understand?', at: 999999, area: 'understand' };
  writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(withForeignQuestion, null, 2) + '\n');
  f.tick();
  const foreignArea = await callCli(['workflow', 'answer', '17', 'ISO']);
  assert.equal(foreignArea.exitCode, 1);
  assert.equal(foreignArea.stderr.trim(), 'No question is open for example/project#17.');
  assert.equal(f.record().changes.length, 2);
});
