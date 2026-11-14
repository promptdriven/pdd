import test from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {existsSync,lstatSync,mkdirSync,readFileSync,readdirSync,symlinkSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {parseArgv} from '../../src/argument-parser.mjs';
import {runPdd} from '../../src/pdd-cli.mjs';
import {runCheck, interfaceBlocks, proseSha256} from '../../src/runtime-seam.mjs';
import {readRunResults,resultLines,usableResult} from '../../src/workflow-results.mjs';
import {readEvidenceEligibility} from '../../src/workflow-runner.mjs';
import {harbor,portsFor,PLACE,root as packageRoot} from './runtime-fake.mjs';

// These are approved native review cases, not executable interpreter scenarios.
const manifestPath = new URL('./runtime/local-lint-result-cases.json',import.meta.url);
const manifestBytes = readFileSync(manifestPath), inventory = JSON.parse(manifestBytes);
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const cli = join(packageRoot,'bin/pdd.mjs'), preload = join(import.meta.dirname,'helpers/local-lint-boundary.mjs');
const time = Date.parse('2026-11-11T12:00:00Z');
const envFor = h => ({HOME:h.home,PDD_STATE_DIR:h.state,PDD_RUNTIME_URL:'invalid'});
const readJson = path => JSON.parse(readFileSync(path,'utf8'));
function tree(root) {
  if (!existsSync(root)) return [];
  return readdirSync(root,{recursive:true}).sort().map(path => {
    const stat = lstatSync(join(root,path));
    return [path,stat.mode,stat.mtimeMs,stat.isFile() ? digest(readFileSync(join(root,path))) : stat.isDirectory() ? 'directory' : 'other'];
  });
}
function guarded(env,now=time) {
  const calls = {authentication:0,network:0,model:0,source:0};
  const denied = name => () => { calls[name]++; assert.fail(`Offline boundary called ${name}`); };
  const p = portsFor(env,{now:()=>now,gh:denied('authentication'),fetch:denied('network'),modelMetadata:denied('model')}).ports;
  return {ports:p,calls};
}
async function command(h,argv,{now=time,env=envFor(h)}={}) {
  const p = guarded(env,now), plan = parseArgv(argv);
  const code = await runCheck({cwd:h.repo,words:[...plan.operands],options:{...plan.options},cache:false},p.ports);
  const json = argv.includes('--json') && p.ports.stdout.text ? JSON.parse(p.ports.stdout.text) : null;
  const names = existsSync(join(env.PDD_STATE_DIR,'batches')) ? readdirSync(join(env.PDD_STATE_DIR,'batches')).filter(name=>/^\d{8}-\d{6}-\w{4}$/.test(name)).sort() : [];
  const batch = json?.batch ?? names.findLast(name=>readJson(join(env.PDD_STATE_DIR,'batches',name,'batch.json')).created_at === new Date(now).toISOString());
  return {...p,code,json,batch,stdout:p.ports.stdout.text,stderr:p.ports.stderr.text,env};
}
function evidence(h,env=envFor(h),since=time) {
  const before = tree(env.PDD_STATE_DIR), calls = {capture:0,workspace:[]};
  const results = readRunResults({root:h.repo,since},{env,capture:()=>{calls.capture++;assert.fail('Local reader recaptured source');},
    workspace:input=>{calls.workspace.push(input);return readEvidenceEligibility(input,{env});}});
  const result = results.find(row=>row.kind==='pdd lint');
  const lines = resultLines(results,{kinds:['pdd lint']});
  assert.deepEqual(tree(env.PDD_STATE_DIR),before,'workflow read must leave state bytes and metadata unchanged');
  return {results,result,lines,calls,unchanged:true};
}
function completed(h,run,expectedExit=run.code) {
  assert.equal(run.code,expectedExit,run.stderr);
  assert.ok(run.batch,'2924 local lint must save a named batch');
  const directory = join(run.env.PDD_STATE_DIR,'batches',run.batch), batch = readJson(join(directory,'batch.json')), summary = readJson(join(directory,'summary.json'));
  assert.deepEqual(Object.keys(batch).sort(),'version batch root created_at intent local_only source_sha256 local_scope summary_line exit_code warnings problems rows lint'.split(' ').sort());
  assert.deepEqual(Object.keys(summary).sort(),'batch repo exit_code state lint_state reason local_only local_scope summary_line warnings problems rows report_url'.split(' ').sort());
  assert.deepEqual(batch.lint,{state:inventory.local_invariants.lint_state,lint_state:inventory.local_invariants.lint_state,reason:inventory.local_invariants.reason,request_ids:[]});
  assert.equal(batch.version,1); assert.equal(batch.root,h.repo); assert.equal(summary.repo,h.repo); assert.equal(batch.batch,run.batch);
  assert.equal(batch.source_sha256,null); assert.equal(summary.exit_code,expectedExit); assert.equal(batch.exit_code,expectedExit);
  for (const key of ['local_scope','warnings','problems','rows','summary_line']) assert.deepEqual(summary[key],batch[key]);
  assert.equal(summary.state,'partial'); assert.equal(summary.local_only,true); assert.equal(summary.report_url,null);
  assert.equal(readJson(join(run.env.PDD_STATE_DIR,'repos',`${digest(h.repo).slice(0,16)}.json`)).last_batch,run.batch);
  if (run.json) assert.deepEqual(run.json,summary,'immediate JSON is the completed saved projection');
  return {batch,summary};
}
function invariants(h,run,view,saved) {
  const inv = inventory.local_invariants;
  assert.equal(saved.batch.intent,inv.saved_intent); assert.equal(saved.batch.local_only,inv.local_only);
  assert.equal(view.result.localOnly,inv.local_only); assert.equal(view.result.state,inv.lint_state);
  assert.equal(view.result.reason.code,inv.reason_code); assert.equal(usableResult(view.result),inv.usableResult);
  assert.deepEqual(view.result.reason,inv.reason); assert.deepEqual(view.result.states,[]); assert.deepEqual(view.result.requests,[]);
  assert.deepEqual(view.result.localScope,saved.batch.local_scope); assert.equal(view.result.source,'unknown');
  assert.equal(view.calls.capture,0); assert.equal(run.calls.authentication,inv.authentication_calls); assert.equal(run.calls.network,inv.network_calls); assert.equal(run.calls.model,inv.model_calls);
  for (const word of inv.forbidden_summary) assert.ok(!view.lines.join('\n').includes(word));
  for (const key of ['engine','model','reports']) assert.ok(!Object.hasOwn(view.result,key));
  assert.ok(!tree(run.env.PDD_STATE_DIR).some(([path])=>/cache|receipt|\.posted$|batch\.lock/.test(path)),'local result creates no pass cache, lint receipt or dispatch files');
  assert.match(view.lines[0],/Scope: (repository scan|tests tests\/place-order.json); prompts /);
  return true;
}
function compare(expected,actual) {
  assert.deepEqual(Object.keys(actual).sort(),Object.keys(expected).sort(),'all approved expectation fields have actual observations');
  for (const [key,value] of Object.entries(expected)) assert.deepEqual(actual[key],value,key);
}
function withWarning(repo) {
  let text = `${readFileSync(join(repo,PLACE),'utf8')}\n![layout](selected.ui.svg)\n`;
  const block = interfaceBlocks(text)[0], iface = JSON.parse(block[1]);
  iface.status = 'draft';
  text = text.slice(0, block.indices[1][0]) + JSON.stringify(iface) + text.slice(block.indices[1][1]);
  text = text.replace(/"prose_sha256"\s*:\s*"[^"]*"/, `"prose_sha256":"${proseSha256(text)}"`);
  writeFileSync(join(repo,PLACE),text);
  writeFileSync(join(repo,'prompts/selected.ui.svg'),'<svg><text>Selected warning</text></svg>');
  writeFileSync(join(repo,'prompts/unrelated.prompt.md'),'![layout](unrelated.ui.svg)');
  writeFileSync(join(repo,'prompts/unrelated.ui.svg'),'<svg><text>Unrelated warning</text></svg>');
}
function missingInterface(repo) { writeFileSync(join(repo,'prompts/missing.prompt.md'),'# Missing Runtime declaration\n'); }
function olderHosted(h,at=time-1000) {
  const name='20261111-115959-old1',directory=join(h.state,'batches',name); mkdirSync(directory,{recursive:true});
  writeFileSync(join(directory,'batch.json'),JSON.stringify({version:1,batch:name,root:h.repo,created_at:new Date(at).toISOString(),intent:'lint-only',
    source_sha256:'a'.repeat(64),rows:[{test:'tests/place-order.json',state:'passed'}],lint:{state:'passed',request_ids:['hosted-control']}}));
  return {name,bytes:readFileSync(join(directory,'batch.json'))};
}
function nativeCli(h,argv,extra={}) {
  return spawnSync(process.execPath,['--import',preload,cli,...argv],{cwd:h.repo,env:{...process.env,...envFor(h),...extra},encoding:'utf8'});
}

for (const vector of inventory.cases) test(`2924 vector: ${vector.id}`,async t=>{
  const e=vector.expected;
  if (vector.id==='default-zero-warning') {
    const h=harbor(t), run=await command(h,vector.argv), saved=completed(h,run,e.exit_code), view=evidence(h);
    compare(e,{exit_code:run.code,saved_batch_and_summary:!!saved.batch&&!!saved.summary,saved_summary_from_setup:saved.summary.summary_line===inventory.setup.default_summary,
      local_scope_tests:saved.batch.local_scope.tests,local_scope_prompts:saved.batch.local_scope.prompts,reader_kind:view.result.kind,
      reader_summary_from_setup:view.result.summary===inventory.setup.default_summary,rendered_partial_and_local_only:/partial.*local-only/.test(view.lines[0]),
      apply_local_invariants:invariants(h,run,view,saved),saved_rows:saved.batch.rows,reader_states:view.result.states,reader_state:view.result.state,
      reader_localOnly:view.result.localOnly,reader_usableResult:usableResult(view.result)});
    // Separate real process uses the unchanged upstream approved Harbor declaration.
    const child= nativeCli(h,['lint','--local','--json']); assert.equal(child.status,e.exit_code,child.stderr);
    const childJson=JSON.parse(child.stdout); assert.deepEqual(readJson(join(h.state,'batches',childJson.batch,'summary.json')),childJson);
    const read=nativeCli(h,['test','--read',childJson.batch,'--json']); assert.equal(read.status,e.exit_code,read.stderr); assert.deepEqual(JSON.parse(read.stdout),childJson);
  } else if (vector.id==='selected-json-with-warning'||vector.id==='default-interface-refusal') {
    const warning=vector.id==='selected-json-with-warning', h=harbor(t,warning?withWarning:missingInterface);
    const run=await command(h,vector.argv), saved=completed(h,run), view=evidence(h), plain=await command(h,vector.also_replay_argv,{now:time+1000});
    const diagnostics=warning?saved.summary.warnings:saved.summary.problems.map(p=>`${p.code}: ${p.message}`);
    const retained=diagnostics.length>0&&diagnostics.every(value=>plain.stdout.includes(value))
      && (warning ? saved.summary.warnings.every(value=>run.json.warnings.includes(value)) : saved.summary.problems.every(item=>run.json.problems.some(actual=>actual.code===item.code&&actual.message===item.message)))
      && (warning ? saved.summary.warnings.every(value=>view.lines[0].includes(value)) : saved.summary.problems.every(p=>view.lines[0].includes(p.code)&&view.lines[0].includes(p.message)));
    assert.ok(!plain.stdout.includes('Scope:'),'existing immediate text gets no new scope line');
    if (warning) compare(e,{exit_code:run.code,json_and_saved_batch_identity_match:run.json.batch===saved.batch.batch,
      json_and_saved_scope_match:JSON.stringify(run.json.local_scope)===JSON.stringify(saved.batch.local_scope),
      selected_scope_only:JSON.stringify(saved.batch.local_scope)===JSON.stringify({tests:['tests/place-order.json'],prompts:[PLACE]}),
      unrelated_warning_absent:!run.json.warnings.some(w=>w.includes('unrelated')),apply_local_invariants:invariants(h,run,view,saved),
      selected_warning_retained_in_text_json_saved_and_reader:retained,immediate_text_keeps_warning_and_partial_summary_without_new_scope_line:plain.stdout.includes(saved.summary.summary_line)&&retained});
    else compare(e,{exit_code:run.code,saved_local_partial_classification:saved.summary.local_only&&saved.summary.state==='partial',apply_local_invariants:invariants(h,run,view,saved),
      original_interface_finding_retained_in_text_json_saved_and_reader:retained,immediate_text_keeps_finding_and_partial_summary:plain.stdout.includes(saved.summary.summary_line)&&retained});
  } else if (vector.id==='offline-command-produced-empty-batch-read') {
    const exits=[],readExits=[]; let allEqual=true,textRetained=true,retrySame=true,stateUnchanged=true,sourceCalls=0,legacyKept=false,common=true,view;
    for (const edit of [undefined,missingInterface]) {
      const h=harbor(t,edit),run=await command(h,vector.argv),saved=completed(h,run);view=evidence(h);
      const before=tree(h.state); exits.push(run.code); common&&=invariants(h,run,view,saved);
      for (const [index,input] of vector.follow_up_public_runCheck_inputs.entries()) {
        const p=guarded(envFor(h));p.ports.captureSource=()=>{sourceCalls++;assert.fail('Saved read must not capture source');};
        const options={...input.options};if (options['--retry'])options['--retry']=run.batch;
        const code=await runCheck({cwd:h.repo,words:input.words.length?[run.batch]:[],options,cache:input.cache},p.ports);
        if (index===0) {readExits.push(code);textRetained&&=p.ports.stdout.text.includes(saved.summary.summary_line)&&saved.summary.problems.every(item=>p.ports.stdout.text.includes(item.message));}
        else {allEqual&&=JSON.stringify(JSON.parse(p.ports.stdout.text))===JSON.stringify(run.json);assert.equal(code,run.code);}
        if (index===2) retrySame&&=/fresh pdd lint --local/.test(p.ports.stderr.text);
        assert.deepEqual(p.calls,{authentication:0,network:0,model:0,source:0});
      }
      // Default --read also uses the repository pointer without changing its bytes.
      const p=guarded(envFor(h));assert.equal(await runPdd(['test','--read','--json'],{cwd:h.repo,...p.ports}),run.code);assert.deepEqual(JSON.parse(p.ports.stdout.text),run.json);
      stateUnchanged&&=JSON.stringify(tree(h.state))===JSON.stringify(before);
      // Legacy native-only control keeps its established nonempty-row route.
      const name='20261111-115958-nat1',dir=join(h.state,'batches',name);mkdirSync(dir);
      writeFileSync(join(dir,'batch.json'),JSON.stringify({version:1,batch:name,root:h.repo,created_at:new Date(time).toISOString(),intent:'lint-only',local_only:true,
        source_sha256:null,rows:[{test:'tests/native.json',story:'native',state:'not_run',unsent:true,request_ids:[],native_only:[{path:PLACE,reason:'Native control'}],refusals:[]}],lint:{state:'not_run',request_ids:[]}}));
      const legacy=guarded(envFor(h));assert.equal(await runCheck({cwd:h.repo,words:[name],options:{'--read':true,'--json':true}},legacy.ports),5);
      const legacyJson=JSON.parse(legacy.ports.stdout.text);legacyKept=legacyJson.rows.length===1&&!Object.hasOwn(legacyJson,'local_scope');
    }
    compare(e,{saved_batch_and_summary_match_shared_contract:allEqual,saved_rows:view.result.states,
      text_and_json_reads_preserve_original_exit_codes:readExits,read_json_batch_scope_summary_reason_warnings_problems_equal_command_json:allEqual,
      text_read_retains_summary_and_diagnostics:textRetained,reader_states:view.result.states,reader_usableResult:usableResult(view.result),
      retry_returns_same_saved_result_and_requests_fresh_local_lint_for_new_evidence:retrySame,invalid_runtime_origin_never_validated:exits.length===2,
      source_capture_calls_during_read_or_retry:sourceCalls,state_tree_unchanged_by_read_and_retry:stateUnchanged,
      no_auth_network_model_dispatch_continuation_lock_or_cache_receipt_writes:stateUnchanged,legacy_native_only_batch_keeps_existing_read_classification:legacyKept,apply_local_invariants:common});
  } else if (vector.id==='newest-local-after-hosted') {
    const h=harbor(t),old=olderHosted(h),run=await command(h,vector.argv),saved=completed(h,run),view=evidence(h,envFor(h),time-2000);
    assert.deepEqual(readFileSync(join(h.state,'batches',old.name,'batch.json')),old.bytes);
    compare(e,{reader_selects_command_local_batch:view.result.batch===run.batch,older_hosted_pass_not_substituted:view.result.batch!==old.name,apply_local_invariants:invariants(h,run,view,saved)});
  } else if (vector.id==='root-time-and-read-only-controls') {
    const h=harbor(t),foreign=harbor(t);await command(h,vector.argv,{now:time-1000});
    const other=await command(foreign,vector.argv,{now:time+1000,env:{...envFor(foreign),PDD_STATE_DIR:h.state}});
    const run=await command(h,vector.argv,{now:time+2000}),saved=completed(h,run),view=evidence(h,envFor(h),time);
    const none=evidence(h,envFor(h),time+3000);
    compare(e,{foreign_and_pre_run_results_excluded:view.results.length===1&&view.result.batch!==other.batch&&none.results.length===0,
      reader_selects_command_local_batch:view.result.batch===run.batch,state_tree_unchanged_by_reads:view.unchanged,no_tests_or_commands_started_by_reader:view.calls.capture===0,
      apply_local_invariants:invariants(h,run,view,saved)});
    assert.deepEqual(view.calls.workspace.map(call=>call.tests),[saved.batch.local_scope.tests,saved.batch.local_scope.tests]);
  } else if (vector.id==='state-inside-repository') {
    const h=harbor(t);writeFileSync(join(h.repo,'old-result.json'),'preserve');
    const original=tree(h.repo),direct=await command(h,vector.argv,{env:{...envFor(h),PDD_STATE_DIR:h.repo}});
    const link=join(h.sandbox,'inside-link');symlinkSync(h.repo,link);const linked=await command(h,vector.argv,{env:{...envFor(h),PDD_STATE_DIR:link}});
    assert.equal(linked.code,e.exit_code); assert.match(linked.stderr,/outside the repo/);
    compare(e,{exit_code:direct.code,clear_external_state_diagnostic:/PDD_STATE_DIR.*inside.*repository.*outside the repo/.test(direct.stderr),
      no_completed_new_result:!existsSync(join(h.repo,'batches')),no_saved_success_claim:direct.stdout==='',previous_results_unchanged:JSON.stringify(tree(h.repo))===JSON.stringify(original),
      network_and_authentication_calls:direct.calls.network+direct.calls.authentication});
  } else if (vector.id==='state-write-failure') {
    const blocked=harbor(t);writeFileSync(blocked.state,'not a directory');const fail=await command(blocked,vector.argv);assert.equal(fail.code,e.exit_code);assert.match(fail.stderr,/Could not save local lint result/);assert.equal(fail.stdout,'');
    const h=harbor(t),old=olderHosted(h,Date.now()-60000),prior=readFileSync(join(h.state,'batches',old.name,'batch.json'));
    const child=nativeCli(h,vector.argv,{PDD_TEST_OBSTRUCT_LOCAL_SUMMARY:'1'});assert.equal(child.status,e.exit_code,child.stderr);
    const names=readdirSync(join(h.state,'batches')).filter(name=>name!==old.name);assert.equal(names.length,1);
    const batch=names[0],view=evidence(h,envFor(h),0),before=tree(h.state),p=guarded(envFor(h));
    const code=await runPdd(['test','--read',batch,'--json'],{cwd:h.repo,...p.ports});const json=JSON.parse(p.ports.stdout.text);
    assert.equal(json.summary_line,view.result.summary);assert.equal(json.exit_code,e.offline_cli_read_of_prepared_batch_exit_code);
    compare(e,{exit_code:child.status,clear_state_save_diagnostic:/Could not save local lint result/.test(child.stderr),
      no_completed_new_result:lstatSync(join(h.state,'batches',batch,'summary.json')).isDirectory(),no_saved_success_claim:child.stdout==='',
      previous_results_unchanged:readFileSync(join(h.state,'batches',old.name,'batch.json')).equals(prior),network_and_authentication_calls:p.calls.network+p.calls.authentication,
      prepared_batch_without_matching_complete_summary_remains_newest_local_candidate:view.result.batch===batch,
      incomplete_reader_state:view.result.state,incomplete_reader_localOnly:view.result.localOnly,incomplete_reader_usableResult:usableResult(view.result),incomplete_reader_summary:view.result.summary,
      older_hosted_pass_not_substituted:view.result.batch!==old.name,offline_cli_read_of_prepared_batch_exit_code:code,reader_state_tree_unchanged:JSON.stringify(tree(h.state))===JSON.stringify(before)});
  } else assert.fail(`Unmapped native case ${vector.id}`);
  assert.deepEqual(readFileSync(manifestPath),manifestBytes,'approved case inventory must stay unchanged');
});
