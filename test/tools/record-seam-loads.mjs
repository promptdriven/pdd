import { writeFileSync } from 'node:fs';
import { SEAM_LOADS_RECORD, seamWorld } from '../helpers/seam-loads.mjs';

const world = seamWorld();
try {
  const lines = [];
  for (const [key, { loaded }] of await world.probeAll()) {
    for (const name of loaded) lines.push(`${key} ${name}`);
  }
  writeFileSync(SEAM_LOADS_RECORD, `${lines.sort().join('\n')}\n`);
} finally {
  world.remove();
}
