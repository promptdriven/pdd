// Sequential public-route control: old code must fail an assertion before any new API test import.
import {spawnSync} from 'node:child_process';
import {mkdtempSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';
const root=resolve(import.meta.dirname,'..'),temporary=mkdtempSync(join(tmpdir(),'pdd-native-proof-'));
const env={...process.env,HOME:temporary,PDD_STATE_DIR:join(temporary,'runtime'),npm_config_cache:join(temporary,'npm-cache'),npm_config_update_notifier:'false'};
const files=['native-cli-integration','native-original-custody','native-packed-cli','native-evidence-intake','native-validation-profile.vectors','native-criterion-evidence.vectors','bounded-workspace-policy.vectors','bounded-runtime-capture.vectors','bounded-simulator-context.vectors','bounded-authored-source.vectors','authored-case-import.vectors','bounded-workspace-migration.vectors','workflow-results'];
try {
 for(const selected of [['test/native-cli-selection.test.mjs'],files.map(name=>'test/'+name+'.test.mjs')]) {
  const result=spawnSync(process.execPath,['--test',...selected],{cwd:root,env,stdio:'inherit'});
  if(result.status!==0){process.exitCode=result.status??1;break;}
 }
}finally{rmSync(temporary,{recursive:true,force:true});}
