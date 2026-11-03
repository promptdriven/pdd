import test from 'node:test';
import { replayRunPddVectors } from './helpers/run-pdd-vectors.mjs';

test('replay approved help-teaches-pdd Story vectors through runPdd', t => replayRunPddVectors(t, 'help-teaches-pdd.json'));
