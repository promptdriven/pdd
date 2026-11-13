import './helpers/test-home.mjs';
import test from 'node:test';
import { replayScenario, assertReplay } from './helpers/workflow-scenario-replay.mjs';

test('workflow-prove: replay exact command forwarding and saved facts through the native public operation', async () => {
  assertReplay(await replayScenario('workflow-prove-literal-command'));
});
