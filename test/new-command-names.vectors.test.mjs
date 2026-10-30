import test from 'node:test';
import { replayRunPddVectors } from './helpers/run-pdd-vectors.mjs';

test('replay approved new-command-names Story vectors through runPdd', t => replayRunPddVectors(t, 'new-command-names.json'));
