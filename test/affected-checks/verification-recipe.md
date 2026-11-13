# Verify affected selection and historical baseline reports

These commands exercise the native public boundaries for the two approved Stories:
`affected-story-selection` and `affected-baseline-report`. The four approved JSON
files are inputs, not generated expectations. No dependency installation is needed
with Node 22.16 or later. Run from the package checkout.

## Controlled native verification

```sh
node --test test/runtime-package/affected-check-plan.vectors.test.mjs test/runtime-package/affected-check-plan.native.test.mjs test/affected-story-selection.vectors.test.mjs test/affected-baseline-report.vectors.test.mjs
```

The selection test starts the actual `bin/pdd.mjs test --affected --json` process
against a temporary Git repository and a local HTTP interpreter fixture. It checks
all A variants and B dispatch, unchanged criteria, exact selected source identity,
no C dispatch, selected rows, and omitted baseline guidance. Other tests call the
public `runCheck`, `readRunResults`, and unchanged `fullCheckPass` boundaries.
They inspect actual saved batches and original matching-ID receipt bytes. They
cover history corruption, all original attempts, complete original-batch source
currentness, retained PR 1/before associations, read/retry snapshots, uncertain
request IDs, cache identity changes, call ceilings, and unchanged gate outcomes.
Production evidence registration and eligibility readers establish historical
stage authority. No fabricated pass callback supplies a baseline verdict.

Every fixture uses a separate temporary Git root, HOME, runtime state and local
HTTP server. Test cleanup removes its own resources. Test logs belong outside the
repository. These tests establish native behavior with controlled external
boundaries. They do not establish hosted model behavior or reproduce the original
431-call incident. That incident remains **NOT REPRODUCED**.

## Actual-command old-code control

Keep this checkout and its tests. Point only the child CLI at an old source tree
that has no `--affected` support:

```sh
PDD_AFFECTED_CLI=/absolute/path/to/old-source/bin/pdd.mjs node --test --test-name-pattern='real CLI selects' test/affected-story-selection.vectors.test.mjs
```

Expected: the assertion `3146_AFFECTED_CLI_NOT_ACCEPTED` fails because the actual
old CLI refuses `test --affected`. The failure must include the unsupported-option
message and its actual status. A missing module, import error, missing fixture or
other pre-target startup failure does not count as this control.

Run the same command without `PDD_AFFECTED_CLI` in the candidate checkout. It must
pass and show actual selected POST effects. Preserve both logs, source revisions,
`git status --short`, `git diff`, UTC times and Node version outside the checkout.
Do not claim that the old unsupported flag reproduces the original cost incident.

## Bounded hosted action (separate evidence)

A verifier with authorized hosted access can repeat the real CLI action below.
This uses the person's existing gh login. It creates no Try session, workflow
chat, approval, publication or merge. The three selected tests each request a cap
of 3; the existing one-replacement policy gives a maximum requested ceiling of 18
calls, not a spend prediction. A refusal or missing usage is not a pass or zero
spend. Record the actual receipt usage and report links.

Set `PDD_VERIFY_EVIDENCE` to an existing private directory outside the checkout.
The command saves the CLI output and original runtime state there. Set
`PDD_VERIFY_GH_CONFIG_DIR` before loading the isolated test helper, because that
helper deliberately isolates HOME.

```sh
PDD_VERIFY_GH_CONFIG_DIR="${GH_CONFIG_DIR:-$HOME/.config/gh}" node --input-type=module <<'NODE'
import {appendFileSync,cpSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {affectedFixture,cli} from './test/helpers/affected-check-fixture.mjs';
const {DEFAULT_RUNTIME_URL}=await (await import('./src/runtime-seam.mjs')).loadRuntimeClient();
const evidence=process.env.PDD_VERIFY_EVIDENCE;
if(!evidence)throw Error('Set PDD_VERIFY_EVIDENCE to a private external evidence directory.');
const cleanup=[];
const setup=affectedFixture({after:fn=>cleanup.push(fn)});
try {
  appendFileSync(join(setup.repo,'docs/shared.md'),'\n');
  const result=await cli(setup,['test','--affected','--json','--max-calls','3'],{
    env:{PDD_RUNTIME_URL:process.env.PDD_RUNTIME_URL??DEFAULT_RUNTIME_URL,
      GH_CONFIG_DIR:process.env.PDD_VERIFY_GH_CONFIG_DIR}
  });
  writeFileSync(join(evidence,'affected-hosted-cli.json'),JSON.stringify({
    at:new Date().toISOString(),entry:'bin/pdd.mjs test --affected --json --max-calls 3',
    exitCode:result.code,stdout:result.stdout,stderr:result.stderr},null,2));
  cpSync(setup.state,join(evidence,'affected-hosted-runtime-state'),{recursive:true});
  const output=JSON.parse(result.stdout);
  if(output.check_selection?.tests?.join(',')!==setup.selected.join(','))throw Error('Unexpected selected tests.');
  if(output.rows.some(row=>row.test==='test/runtime/C.json'))throw Error('Omitted C received a current row.');
  if(!output.warnings.includes('Affected checks only; this is not a full workflow pass. Required full-pass gates still apply.'))throw Error('Missing selection disclaimer.');
  process.stdout.write(JSON.stringify({exitCode:result.code,selected:output.check_selection,
    baselineAvailability:output.baseline_report?.availability,rows:output.rows.map(row=>({test:row.test,state:row.state,calls:row.calls,report_url:row.report_url}))})+'\n');
  process.exitCode=result.code;
} finally {
  for(const fn of cleanup.reverse())await fn();
}
NODE
```

Readiness, actual command execution, selected membership, individual criterion
results, receipts, accounting, and cleanup are separate observations. Report each
as passed, failed, unavailable, or not run. An authenticated hosted call alone does
not prove criteria passed. Missing local baseline history must remain missing.
Never insert a saved baseline observation into current batch rows to obtain a
full pass. The independent verifier records all remaining unexecuted native case
variants and the actual scope of any hosted result.
