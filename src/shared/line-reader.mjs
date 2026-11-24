// Layer-0 sequential stdin line reader for Simulator CLI doors.
import { createInterface } from 'node:readline';

export function lineReader(stdin) {
  const reader = createInterface({ input: stdin });
  const lines = [];
  const waiting = [];
  let closed = false;
  reader.on('line', text => {
    const next = waiting.shift();
    if (next) next(text);
    else lines.push(text);
  });
  reader.on('close', () => {
    closed = true;
    for (const next of waiting.splice(0)) next('');
  });
  return {
    ask: () => (lines.length ? Promise.resolve(lines.shift()) : closed ? Promise.resolve('') : new Promise(done => waiting.push(done))),
    close: () => reader.close(),
  };
}
