import fs from 'node:fs';
import {replayCases} from './helpers/local-contract-replay.mjs';

const fixturePath = new URL('./shared-contracts/local-contract-writers.json',import.meta.url);
const vectors = JSON.parse(fs.readFileSync(fixturePath,'utf8'));
replayCases(vectors,'contract writers replay',fixturePath);
