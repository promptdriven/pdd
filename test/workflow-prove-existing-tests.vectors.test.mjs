import test from 'node:test';
import { replayScenario, assertReplay } from './helpers/workflow-scenario-replay.mjs';
test('workflow-prove-existing-tests: replay all approved public operations and exact checks', async () => assertReplay(await replayScenario('workflow-prove-existing-tests')));
