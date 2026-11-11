import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { releaseNotice } from '../src/release-notice.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/release-notice.json', import.meta.url)));
const at = (value, path) => path.slice(1).split('/').reduce((value, key) => value[key], value);
for (const step of scenario.steps) test(`release-notice vector: ${step.step_id}`, async () => {
  const calls = {resources:{'release-notice-releases-latest':0}};
  const result = await releaseNotice(step.input, {releases:{latest:async input => {
    assert.deepEqual(input, {});
    calls.resources['release-notice-releases-latest']++;
    return structuredClone(scenario.simulation['releases.latest'].result_template);
  }}});
  for (const check of step.checks) {
    assert.equal(check.op, 'equals');
    assert.deepEqual(at({result,calls}[check.target], check.path), check.value, check.criterion_id);
  }
});

test('release read rejection and invalid replies are silent', async () => {
  for (const reply of [null, undefined, {}, {tag:1}, {tag:'v01.2.3'}, {tag:'v9007199254740992.0.0'}, {tag:'v9.0.0; echo bad'}, {tag:'v9.0.0\n'}, {tag:'v9.0.0-rc.1'}]) {
    assert.deepEqual(await releaseNotice({version:'1.0.0',ci:false,probe:false}, {releases:{latest:async () => reply}}), {message:''});
  }
  assert.deepEqual(await releaseNotice({version:'1.0.0',ci:false,probe:false}, {releases:{latest:async () => {throw Error('secret');}}}), {message:''});
});

test('malformed installed versions never read releases', async () => {
  for (const version of ['01.0.0', '1.0', '1.0.0-01', '1.0.0-', '1.0.0+', '1.0.0\n', '9007199254740992.0.0']) {
    assert.deepEqual(await releaseNotice({version,ci:false,probe:false}, {releases:{latest:async () => assert.fail('unexpected read')}}), {message:''});
  }
});

test('valid long build metadata does not suppress a newer release', async () => {
  const version = '1.0.0+' + 'a'.repeat(1024);
  let calls = 0;
  const result = await releaseNotice({version,ci:false,probe:false}, {releases:{latest:async () => {calls++; return {tag:'v2.0.0'};}}});
  assert.equal(calls, 1);
  assert.equal(result.message, `pdd 2.0.0 is available (installed ${version}). Update: npm install -g github:promptdriven/pdd#v2.0.0`);
});
