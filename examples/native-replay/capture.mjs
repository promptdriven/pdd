// Generated from examples/native-replay/capture.prompt.md.
import {run} from 'node:test';
import {createHash} from 'node:crypto';
import {readFileSync, mkdirSync, writeFileSync} from 'node:fs';
import {resolve, relative} from 'node:path';
import {captureSource} from '../../src/runtime-preflight.mjs';

const [directory, stage = 'current', ...extra] = process.argv.slice(2);
if (!directory || extra.length || !['current','before'].includes(stage)) throw Error('usage: node capture.mjs DIRECTORY [current|before]');
const root = process.cwd();
const sourcePaths = ['examples/native-replay/replay.mjs','examples/native-replay/count-words.mjs','examples/native-replay/cases.json','examples/native-replay/capture.mjs','examples/native-replay/capture.prompt.md'];
const testPaths = ['test/native-replay-recipe-3160.test.mjs'];
const paths = [...sourcePaths, ...testPaths, 'examples/native-replay/replay.prompt.md'];
const hashPaths = paths => createHash('sha256').update(Buffer.concat(paths.map(path => Buffer.concat([Buffer.from(`${path}\0`),readFileSync(path),Buffer.from('\0')])))).digest('hex');
const identity = () => ({sourceId:captureSource(root,{tests:paths,appMap:null}).sha256,implementationId:hashPaths(sourcePaths),testsId:hashPaths(testPaths)});
const before = identity(), events = [];
const serialize = value => JSON.parse(JSON.stringify(value, (_key, item) => {
  if (item instanceof Error) return Object.fromEntries([...new Set(['name','message','stack',...Object.getOwnPropertyNames(item)])].map(key=>[key,item[key]]));
  if (typeof item === 'bigint') return String(item);
  return item;
}));
const stream = run({files:testPaths.map(path=>resolve(path))});
for await (const event of stream) {
  const original = serialize(event.data);
  const data = {...original};
  if (data.file) data.file = relative(root,data.file).split('\\').join('/');
  events.push({type:event.type,data,original});
}
if (JSON.stringify(identity()) !== JSON.stringify(before)) throw Error('source changed during capture');
const failed = events.some(event => event.type === 'test:fail');
const ended = events.some(event => event.type === 'test:plan' && event.data.nesting === 0);
if (!ended) throw Error('test runner did not complete');
const save = (name, data) => writeFileSync(resolve(directory,name),JSON.stringify(data));
mkdirSync(directory,{recursive:true});
save('report.json',{schema:'pdd.native-node-report.v1',producerVersion:'1.0',runnerVersion:process.versions.node,runtimeVersion:process.versions.node,source:before,events});
save('source.json',{producerRoot:root,tests:paths,source_sha256:before.sourceId,source:before,stage});
save('selection.json',{sourceId:before.sourceId,stage,complete:true,testIds:events.filter(e=>e.type==='test:enqueue' && !(e.data.nesting===0 && e.data.line===1 && e.data.column===1 && e.data.name===resolve(e.data.file))).map(({data})=>`${data.file}::${data.name}@${data.line}:${data.column}`)});
save('execution.json',{sourceId:before.sourceId,stage,processEnded:true,exitCode:failed?1:0,producer:'pdd-node-test-events',producerVersion:'1.0',runner:'node:test',runnerVersion:process.versions.node,runtimeVersion:process.versions.node});
save('import.json',{schema:'pdd.native-evidence-import.v1',profileId:'replay',storyPath:'user_stories/native-replay-recipe-3160.md',originals:['report','source','selection','execution'].map(role=>({role,path:`${role}.json`}))});
if (failed) process.exitCode = 1;
