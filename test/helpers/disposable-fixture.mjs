import { mkdtempSync, realpathSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

// Register children immediately after spawn, so even a failed assertion waits
// for their close events before removing files they may still be writing.
export function disposableFixture(t, prefix) {
  const path = realpathSync(mkdtempSync(join(tmpdir(), prefix))), stops = [];
  t.after(async () => {
    const results = await Promise.allSettled(stops.map(stop => stop()));
    const errors = results.filter(result => result.status === 'rejected').map(result => result.reason);
    if (errors.length) throw new AggregateError(errors, 'Disposable children did not stop');
    rmSync(path, { recursive: true, force: true });
  });
  const ownChild = (child, signal = 'SIGKILL') => {
    const closed = new Promise(resolve => child.once('close', resolve));
    const stop = async () => {
      if (child.exitCode === null && child.signalCode === null) child.kill(signal);
      await closed;
    };
    stops.push(stop);
    return stop;
  };
  return { path, ownChild };
}
