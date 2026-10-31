import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { isAbsolute, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { CommandInputError, parseArgv } from '../src/argument-parser.mjs';
import { PUBLIC_COMMAND_MANIFEST } from '../src/command-catalog.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

// Node checks of user_stories/help-teaches-pdd.md that the PDD interpreter cannot make: the two printed paths
// are real files of the pdd package that runs, and help stays local (no network, no skills, no written file).
const root = realpathSync(fileURLToPath(new URL('..', import.meta.url)));
const ROOT_HELP = [[], ['--help'], ['-h'], ['-help'], ['help']];
const TOPIC = ['help', 'prompting'];
const FILES = { guide: 'docs/prompting-guide.md', runbook: 'RUNBOOK.md' };
const sink = () => ({ text: '', write(value) { this.text += value; return true; } });
const temp = t => { const p = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-help-'))); t.after(() => rmSync(p, { recursive: true, force: true })); return p; };
const lines = text => text.replace(/\n$/, '').split('\n');
const formLine = ({ form, description }) => `  ${form}  ${description}`;
const noRunner = new Proxy({}, { get() { assert.fail('Help must not reach the workflow runner'); } });
async function pdd(argv, extra = {}) {
  const stdout = sink(), stderr = sink();
  const exit = await runPdd(argv, { stdout, stderr, workflowRunner: noRunner, ...extra });
  return { exit, stdout: stdout.text, stderr: stderr.text };
}
// The path on the one line that ends with the file name: from the first slash to the end of the line.
function namedPaths(text) {
  return Object.fromEntries(Object.entries(FILES).map(([key, file]) => {
    const found = lines(text).filter(line => line.endsWith(`/${file}`));
    assert.equal(found.length, 1, `one line names ${file}: ${text}`);
    return [key, found[0].slice(found[0].indexOf('/'))];
  }));
}
function assertPackagePaths(text, packageRoot) {
  const paths = namedPaths(text);
  for (const [key, file] of Object.entries(FILES)) {
    assert.ok(isAbsolute(paths[key]), paths[key]);
    assert.equal(paths[key], join(packageRoot, file));
    assert.ok(existsSync(paths[key]), `${paths[key]} exists`);
  }
  assert.ok(JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).bin.pdd, 'the folder is a pdd package');
}

test('root help and pdd help prompting name the guide and RUNBOOK of this package as absolute paths that exist', async () => {
  for (const argv of [...ROOT_HELP, TOPIC]) {
    const result = await pdd(argv);
    assert.equal(result.exit, 0, argv.join(' ')); assert.equal(result.stderr, '', argv.join(' '));
    assertPackagePaths(result.stdout, root);
  }
});

test('the paths come from the module location, never from the cwd', async t => {
  const elsewhere = temp(t);
  for (const argv of [['help'], TOPIC]) {
    assertPackagePaths((await pdd(argv, { cwd: elsewhere })).stdout, root);
    const injected = (await pdd(argv, { packageRoot: join(elsewhere, 'pkg') })).stdout;
    assert.deepEqual(namedPaths(injected), { guide: join(elsewhere, 'pkg', FILES.guide), runbook: join(elsewhere, 'pkg', FILES.runbook) });
  }
  // A copy of the package, run from another folder, names its own files.
  const copy = join(elsewhere, 'copy'), cwd = join(elsewhere, 'work');
  for (const part of ['bin', 'src', 'docs', 'RUNBOOK.md', 'package.json']) cpSync(join(root, part), join(copy, part), { recursive: true });
  mkdirSync(cwd);
  for (const argv of [['help'], TOPIC]) {
    const result = spawnSync(process.execPath, [join(copy, 'bin', 'pdd.mjs'), ...argv], { cwd, encoding: 'utf8', timeout: 5000 });
    assert.equal(result.status, 0, result.stderr); assert.equal(result.stderr, '');
    assertPackagePaths(result.stdout, copy);
  }
  assert.deepEqual(readdirSync(cwd), []);
});

test('help is local: no network, no child process, an empty HOME and no PDD skills', t => {
  const sandbox = temp(t), home = join(sandbox, 'home'), cwd = join(sandbox, 'work'), log = join(sandbox, 'forbidden.log');
  mkdirSync(home); mkdirSync(cwd);
  const guard = join(sandbox, 'guard.mjs');
  writeFileSync(guard, `import fs from 'node:fs';import http from 'node:http';import https from 'node:https';import net from 'node:net';import tls from 'node:tls';import dns from 'node:dns';import child from 'node:child_process';import {syncBuiltinESMExports} from 'node:module';
const append=fs.appendFileSync, home=process.env.HOME;
const stop=what=>()=>{append(${JSON.stringify(log)},what+'\\n');throw Error('Forbidden in help: '+what);};
for(const x of [http,https]){x.request=stop('http');x.get=stop('http');}
net.connect=stop('socket');net.createConnection=stop('socket');tls.connect=stop('tls');dns.lookup=stop('dns');globalThis.fetch=stop('fetch');
for(const key of ['spawn','spawnSync','exec','execSync','execFile','execFileSync','fork'])child[key]=stop('child_process.'+key);
for(const key of ['readFileSync','readdirSync','statSync','lstatSync','existsSync','accessSync','opendirSync','writeFileSync','mkdirSync','cpSync']){
  const original=fs[key];fs[key]=function(path,...rest){if(String(path)===home||String(path).startsWith(home+'/'))stop('fs.'+key+' in HOME')();return original.call(this,path,...rest);};}
syncBuiltinESMExports();`);
  const env = { HOME: home, PATH: '', CLAUDE_CONFIG_DIR: '' };
  for (const argv of [...ROOT_HELP, TOPIC]) {
    const result = spawnSync(process.execPath, ['--import', guard, join(root, 'bin', 'pdd.mjs'), ...argv], { cwd, env, encoding: 'utf8', timeout: 5000 });
    assert.equal(result.status, 0, `${argv.join(' ')}: ${result.stderr}`); assert.equal(result.stderr, '', argv.join(' '));
    assertPackagePaths(result.stdout, root);
  }
  assert.equal(existsSync(log), false, existsSync(log) ? readFileSync(log, 'utf8') : '');
  assert.deepEqual(readdirSync(home), []); assert.deepEqual(readdirSync(cwd), []);
});

test('prompting is a help topic, not a command, and takes no other word', async () => {
  assert.deepEqual(parseArgv(TOPIC), { commandId: 'help', local: 'help', helpPrefix: [], topic: 'prompting' });
  assert.equal(parseArgv(['help']).topic, undefined);
  const unknown = await pdd(['prompting']);
  assert.equal(unknown.exit, 2); assert.equal(unknown.stdout, '');
  assert.equal(lines(unknown.stderr).length, 1); assert.ok(unknown.stderr.includes('Unknown command') && unknown.stderr.includes('prompting'), unknown.stderr);
  for (const argv of [['prompting', '--help'], ['prompting', '-h'], ['help', 'prompting', 'extra'], ['help', 'prompting', '--help'],
    ['help', 'prompting', '-h'], ['help', 'prompting', 'prompting'], ['help', 'prompting', 'test']]) {
    assert.throws(() => parseArgv(argv), CommandInputError, argv.join(' '));
    const refused = await pdd(argv);
    assert.equal(refused.exit, 2, argv.join(' ')); assert.equal(refused.stdout, '', argv.join(' '));
    assert.equal(lines(refused.stderr).length, 1, argv.join(' '));
  }
});

test('root help keeps its first line, every form line and its closing lines; command help is unchanged', async () => {
  const outputs = await Promise.all(ROOT_HELP.map(argv => pdd(argv)));
  for (const output of outputs) assert.equal(output.stdout, outputs[0].stdout);
  const rootHelp = lines(outputs[0].stdout), scoped = lines((await pdd(['test', '--help'])).stdout);
  const testRows = PUBLIC_COMMAND_MANIFEST.filter(({ form }) => form.split(' ')[1] === 'test').map(formLine);
  // Command help: first line, empty line, its own forms, empty line and the three closing lines; no learn or path lines.
  assert.equal(scoped[1], ''); assert.deepEqual(scoped.slice(2, 2 + testRows.length), testRows); assert.equal(scoped[2 + testRows.length], '');
  const closing = scoped.slice(3 + testRows.length);
  assert.equal(closing.length, 3); assert.match(closing.at(-1), /never merges/);
  assert.doesNotMatch(scoped.join('\n'), /help prompting|prompting-guide\.md|RUNBOOK\.md/);
  // Root help: the same first line, every catalog form in order, the learn line and two path lines, the same closing lines.
  const all = PUBLIC_COMMAND_MANIFEST.map(formLine);
  assert.ok(all.some(line => line.startsWith('  pdd help prompting  ')));
  assert.equal(rootHelp[0], scoped[0]); assert.ok(rootHelp[0].startsWith('PDD'));
  assert.equal(rootHelp[1], ''); assert.deepEqual(rootHelp.slice(2, 2 + all.length), all);
  const rest = rootHelp.slice(2 + all.length);
  assert.equal(rest[0], ''); assert.equal(rest[4], ''); assert.deepEqual(rest.slice(5), closing);
  assert.ok(rest[1].includes('pdd help prompting'), rest[1]);
  assert.ok(rest[2].endsWith(`/${FILES.guide}`) && rest[3].endsWith(`/${FILES.runbook}`), rest.join('\n'));
  // The topic: the same first line, the steps, then only the two path lines; no closing lines.
  const topic = lines((await pdd(TOPIC)).stdout);
  assert.equal(topic[0], rootHelp[0]); assert.equal(topic[1], ''); assert.equal(topic.at(-3), '');
  assert.deepEqual(topic.slice(-2), rest.slice(2, 4));
  for (const line of closing) assert.ok(!topic.includes(line), line);
  const text = topic.join('\n');
  for (const name of ['prompts/NAME.prompt.md', '## Dependencies', 'Runtime interface', 'user_stories/STORY.md', 'Acceptance criteria',
    'tests/STORY.json', 'pdd test --fill-hash', 'pdd lint', 'pdd approve']) assert.ok(text.includes(name), name);
  for (const pattern of [/\bpdd check\b/, /\bpdd try\b/, /\bworkflow start\b/, /simulat/i]) {
    assert.doesNotMatch(text, pattern); assert.doesNotMatch(rest.join('\n'), pattern);
  }
});
