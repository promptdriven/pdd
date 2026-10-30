import test from 'node:test';
import { replayScenario, assertReplay } from './helpers/workflow-scenario-replay.mjs';
test('workflow-prove: replay all approved public operations and exact checks', async () => assertReplay(await replayScenario('workflow-prove')));
