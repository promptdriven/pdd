import { writeFileSync } from 'node:fs';
import { SEAM_LOADS_RECORD, seamWorld } from '../helpers/seam-loads.mjs';

const world = seamWorld();
try {
  const loaders = new Map();
  for (const [key, { loaded }] of await world.probeAll()) {
    for (const name of loaded) loaders.set(name, [...(loaders.get(name) ?? []), key]);
  }
  const lines = [...loaders.keys()].sort().map(name => `  ${JSON.stringify(name)}: [${loaders.get(name).map(key => JSON.stringify(key)).join(', ')}],`);
  writeFileSync(SEAM_LOADS_RECORD, `export default {\n${lines.join('\n')}\n};\n`);
} finally {
  world.remove();
}
