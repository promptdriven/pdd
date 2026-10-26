import { readFile } from 'node:fs/promises';
import { buildBootstrap } from '../../launcher/build-bootstrap.mjs';

const [, , descriptorPath, destination] = process.argv;
if (!descriptorPath || !destination) throw new Error('descriptor and destination are required');
const descriptor = JSON.parse(await readFile(descriptorPath, 'utf8'));
await buildBootstrap({ descriptor, destination });
