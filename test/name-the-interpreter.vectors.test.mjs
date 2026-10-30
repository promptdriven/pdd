import test from 'node:test';
import { replayRunPddVectors } from './helpers/run-pdd-vectors.mjs';

test('replay approved name-the-interpreter Story vectors through runPdd', t => replayRunPddVectors(t, 'name-the-interpreter.json'));
