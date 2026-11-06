import { spawn } from 'node:child_process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

function filteredEnvironment(environment) {
  return environment.filter(({ name }) => !name.startsWith('HERDR_') && name !== 'PDD_AGENT_SESSION');
}

function runNodeTest({ cwd, args, environment, stdio }) {
  return spawn(process.execPath, args, {
    cwd,
    env: Object.fromEntries(environment.map(({ name, value }) => [name, value])),
    stdio,
  });
}

export async function runTestSuite({ cwd, testFiles, environment }, ports = { nodeTest: { run: runNodeTest } }) {
  const selectedFiles = testFiles.length ? testFiles : ['test/*.test.mjs'];
  const child = ports.nodeTest.run({
    cwd,
    args: ['--test', ...selectedFiles],
    environment: filteredEnvironment(environment),
    stdio: ['ignore', 'pipe', 'pipe'],
  });

  child.stdout.on('data', chunk => process.stdout.write(chunk));
  child.stderr.on('data', chunk => process.stderr.write(chunk));

  const exit_code = await new Promise(resolveCode => child.once('close', resolveCode));
  return { exit_code };
}

if (process.argv[1] && pathToFileURL(resolve(process.argv[1])).href === import.meta.url) {
  const environment = Object.entries(process.env).map(([name, value]) => ({ name, value }));
  const { exit_code } = await runTestSuite({
    cwd: process.cwd(),
    testFiles: process.argv.slice(2),
    environment,
  });
  process.exitCode = exit_code;
}
