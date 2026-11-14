import { writeFileSync } from 'node:fs';
import { SEAM_LOADS_RECORD, recordLines, seamWorld } from '../helpers/seam-loads.mjs';

const world = seamWorld();
try {
  writeFileSync(SEAM_LOADS_RECORD, `${recordLines(await world.probeAll()).join('\n')}\n`);
} finally {
  world.remove();
}
