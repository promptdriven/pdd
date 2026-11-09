import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as dependencyGithub from '../src/issue-dependencies-github.mjs';
const { readDependencySnapshot } = dependencyGithub;
const readManualHold = dependencyGithub.readManualHold ?? (async () => ({held:false, known:false}));
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { sortPlan } from '../src/issue-sort.mjs';

const repository = 'owner/repo', key = `https://github.com/${repository}/issues/1`;
function fixture() {
  const state = { labels: ['pdd:manual'], events: [], permission: { known: true, allowed: true } };
  const raw = () => ({ id: 1, number: 1, html_url: key, title: 'One', body: '', state: 'open', user: { login: 'owner' }, labels: state.labels.map(name => ({name})), assignees: [] });
  const ports = {
    github: {
      issue: async () => ({json: JSON.stringify(raw())}),
      page: async ({kind, cursor}) => ({json: JSON.stringify({items: kind === 'issues' ? [raw()] : kind === 'timeline' ? (cursor ? state.events.slice(1) : state.events.slice(0, 1)) : [], next: kind === 'timeline' && !cursor && state.events.length > 1 ? 'next' : ''})}),
    },
    manualAuthority: { read: async () => state.permission },
    authority: { read: async () => ({authority:'trusted'}) },
    context: { read: async () => ({json: JSON.stringify({inputs:[], conditions:[], execution:[]})}) },
    owners: { read: async () => ({json: JSON.stringify({claims:[], runs:[], runsKnown:true})}) },
    clock: { now: async () => ({iso:'2026-01-01T00:00:00Z'}) },
  };
  return {state, ports};
}
const event = (event, login) => ({event, label:{name:'pdd:manual'}, actor:{login}});
test('manual hold uses the last current application and repository permission', async () => {
  const {state, ports} = fixture();
  state.events = [event('labeled','writer')];
  assert.deepEqual(await readManualHold({repository, issue:1}, ports), {held:true, known:true});
  state.events.push(event('unlabeled','writer'), event('labeled','outsider'));
  state.permission = {known:true, allowed:false};
  assert.deepEqual(await readManualHold({repository, issue:1}, ports), {held:false, known:true});
  state.permission = {known:false, allowed:false};
  assert.deepEqual(await readManualHold({repository, issue:1}, ports), {held:false, known:false});
  state.labels = [];
  assert.deepEqual(await readManualHold({repository, issue:1}, ports), {held:false, known:true});
});
test('snapshot and sort exclude effective manual holds and restore intake after removal', async () => {
  const {state, ports} = fixture(); state.events = [event('labeled','writer')];
  const read = async () => (await readDependencySnapshot({repository}, ports)).snapshot;
  const held = await read();
  assert.ok(held.issues[0].holds.includes('pdd:manual'));
  assert.equal(projectIssueGraph({snapshot:held}).nodes[0].eligible, false);
  held.sortContext = {release:'x', areas:[], groups:[]};
  assert.deepEqual(sortPlan({snapshot:held}).queued, []);
  state.labels = [];
  const released = await read(); released.sortContext = {release:'x', areas:[], groups:[]};
  assert.ok(!released.issues[0].holds.includes('pdd:manual'));
  assert.deepEqual(sortPlan({snapshot:released}).queued, [key]);
});
