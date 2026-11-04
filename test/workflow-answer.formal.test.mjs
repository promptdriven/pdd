import test from 'node:test';
import assert from 'node:assert/strict';
import * as runner from '../src/workflow-runner.mjs';

function makeRun({ state, questionVariant, gateVariant }) {
  const gate = gateVariant === 'open_gate' ? { kind: 'approve', area: 'story', at: 200 } : null;
  let question = null;
  if (questionVariant === 'open_current') {
    question = { text: 'Which format?', at: 250, area: 'story' };
  } else if (questionVariant === 'open_newer_than_gate') {
    question = { text: 'Confirm before gate?', at: 300, area: 'story' };
  } else if (questionVariant === 'stale_older_than_gate') {
    question = { text: 'Old question?', at: 100, area: 'story' };
  } else if (questionVariant === 'other_area') {
    question = { text: 'Earlier area question?', at: 300, area: 'understand' };
  }
  return {
    repo: 'acme/widgets',
    number: 2576,
    state,
    area: 1,
    areas: [
      { name: 'understand', steps: ['scope'] },
      { name: 'story', steps: ['prompt-story', 'check'] }
    ],
    question,
    gate,
    changes: [{ stage: 'story', round: 1, text: 'Prior request' }]
  };
}

function isQuestionOpen(run) {
  if (!run.question) return false;
  if (run.question.area && run.question.area !== run.areas[run.area]?.name) return false;
  if (run.gate && run.question.at < run.gate.at) return false;
  return true;
}

test('workflow-answer formal: exhaustive bounded check of Rules 1-4 across 480 states', async () => {
  assert.equal(typeof runner.answerRun, 'function', 'answerRun is exported');
  assert.equal(typeof runner.changeRun, 'function', 'changeRun is exported');

  const modes = ['answer', 'changes'];
  const states = ['running', 'waiting', 'completed', 'cancelled'];
  const questionVariants = ['none', 'open_current', 'open_newer_than_gate', 'stale_older_than_gate', 'other_area'];
  const gateVariants = ['none', 'open_gate'];
  const textVariants = [
    { id: 'plain', text: 'Use ISO 8601', approvalLike: false, blank: false },
    { id: 'approval_like', text: 'I approve', approvalLike: true, blank: false },
    { id: 'blank', text: '   ', approvalLike: false, blank: true }
  ];
  const chatOutcomes = [true, false];

  let checked = 0;

  for (const mode of modes) {
    for (const state of states) {
      for (const questionVariant of questionVariants) {
        for (const gateVariant of gateVariants) {
          for (const textSpec of textVariants) {
            for (const chatOk of chatOutcomes) {
              checked++;
              const initial = makeRun({ state, questionVariant, gateVariant });
              const snapshotBefore = structuredClone(initial);
              const sendCalls = [];
              const saveCalls = [];
              let savedRun = structuredClone(initial);

              const ports = {
                runs: {
                  async load({ ref }) {
                    return { run: ref === '2576' ? structuredClone(savedRun) : null };
                  },
                  async save({ ref, run }) {
                    saveCalls.push({ ref, run: structuredClone(run) });
                    savedRun = structuredClone(run);
                    return { ok: true };
                  }
                },
                chat: {
                  async send(call) {
                    sendCalls.push(structuredClone(call));
                    return { ok: chatOk };
                  }
                }
              };

              const fn = mode === 'answer' ? runner.answerRun : runner.changeRun;
              const result = await fn({ ref: '2576', text: textSpec.text }, ports);

              const active = state === 'running' || state === 'waiting';
              const questionOpen = isQuestionOpen(initial);
              const isAnswerFlow = mode === 'answer' || questionOpen;

              // Rule 1: answerRun succeeds only when the run is active and has an open question (and nonblank text + chatOk).
              if (mode === 'answer' && (!active || !questionOpen || textSpec.blank || !chatOk)) {
                assert.notEqual(result.exitCode, 0, `Rule 1 violated for ${JSON.stringify({ mode, state, questionVariant, gateVariant, text: textSpec.id, chatOk })}`);
              }

              // Rule 2: When answerRun refuses because no question is open, chat.send and runs.save are not called and saved run is unchanged.
              if (mode === 'answer' && active && !textSpec.blank && !questionOpen) {
                assert.equal(result.exitCode, 1);
                assert.equal(result.message, 'No question is open for acme/widgets#2576.');
                assert.equal(sendCalls.length, 0, 'Rule 2: chat.send must not be called when no question is open');
                assert.equal(saveCalls.length, 0, 'Rule 2: runs.save must not be called when no question is open');
                assert.deepEqual(savedRun, snapshotBefore, 'Rule 2: saved run must remain unchanged');
              }

              // Check successful deliveries for Rules 1, 3, and 4.
              const shouldSucceed =
                active &&
                !textSpec.blank &&
                (mode === 'answer' ? questionOpen : true) &&
                !(
                  !isAnswerFlow &&
                  gateVariant === 'open_gate' &&
                  textSpec.approvalLike
                ) &&
                chatOk;

              if (shouldSucceed) {
                assert.equal(result.exitCode, 0, `Expected success for ${JSON.stringify({ mode, state, questionVariant, gateVariant, text: textSpec.id, chatOk })}`);
                assert.equal(sendCalls.length, 1);
                assert.equal(saveCalls.length, 1);
                const lastChange = savedRun.changes.at(-1);
                assert.equal(lastChange.text, textSpec.text);

                // Rule 3: Every delivered answer clears run.question to null and records { answer: true };
                // every delivered change request when no question is open records a run.changes entry without answer: true.
                if (isAnswerFlow) {
                  assert.equal(savedRun.question, null, 'Rule 3: delivered answer must clear run.question');
                  assert.equal(lastChange.answer, true, 'Rule 3: delivered answer must record answer: true');
                } else {
                  assert.equal(Object.hasOwn(lastChange, 'answer'), false, 'Rule 3: delivered change request must not set answer: true');
                }

                // Rule 4: Answering an open question when run.gate is also present leaves run.gate intact
                // and run.state as waiting, even if the answer text looks like an approval.
                if (isAnswerFlow && gateVariant === 'open_gate') {
                  assert.deepEqual(savedRun.gate, snapshotBefore.gate, 'Rule 4: run.gate must remain intact');
                  assert.equal(savedRun.state, 'waiting', 'Rule 4: run.state must remain waiting at an open gate');
                } else if (isAnswerFlow && gateVariant === 'none') {
                  assert.equal(savedRun.state, 'running', 'Answered question without gate returns run to running');
                }
              } else {
                assert.notEqual(result.exitCode, 0);
                assert.equal(saveCalls.length, 0);
                assert.deepEqual(savedRun, snapshotBefore);
              }
            }
          }
        }
      }
    }
  }

  assert.equal(checked, 480);
});
