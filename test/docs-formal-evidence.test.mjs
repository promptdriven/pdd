import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';

const read = path => readFileSync(new URL(`../${path}`, import.meta.url), 'utf8').replace(/\s+/g, ' ');

// #3139: following either public contract must give the same small-change readiness policy.
for (const path of ['docs/replay-evidence.md', 'skills/pdd-prompting/runbook/autopilot-and-checklists.md']) {
  test(`${path} requires the one-PR small-change formal record and scoped docs exemption`, () => {
    const text = read(path);
    assert.match(text, /one-PR small-change[^.]*recorded formal result/i, path);
    assert.match(text, /missing formal evidence[^.]*waits[^.]*before[^.]*formal[^.]*completion[^.]*blocks[^.]*after/i, path);
    assert.match(text, /documentation-only[^.]*not_applicable[^.]*scope[^.]*reason[^.]*control_outcome[^.]*not_run/i, path);
    assert.match(text, /other workflows[^.]*step-completion policy[^.]*known Story[^.]*Rules to check/i, path);
  });
}

test('replay docs exclude one-PR small-change from the no-rules not-needed policy', () => {
  const text = read('docs/replay-evidence.md');
  const notNeeded = text.match(/[^.]*Formal check: not needed[^.]*\./)?.[0];
  assert.ok(notNeeded);
  assert.match(notNeeded, /outside[^.]*one-PR small-change/i);
});
