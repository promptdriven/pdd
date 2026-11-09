# Native test home isolation

Own the native test environment in `test/helpers/test-home.mjs` and its use by
`package.json`, test entrypoints and shared fixtures. This is a test harness
contract. Preserve production path rules, public commands, fixture fakes and
existing behavioral expectations.

Before a test can use a default home path, give its process a fresh temporary
HOME. This includes `os.homedir()` fallbacks when an injected environment omits
HOME, default workflow state, interpreter state, Herdr config and installed
agent skills. Clear inherited state and agent/config directory overrides so they
cannot redirect a fixture into the caller's folders. Keep explicit fixture
homes and state directories available to tests that exercise path selection.
A missing interpreter state override uses the normal default under the temporary
HOME. Do not set an inherited interpreter directory that wins over a fixture's
own HOME. Do not inspect, copy or change the caller's home or credentials.

An OS account lookup (`os.userInfo`) bypasses HOME. Deny an un-injected lookup
before reading the account database and fail the test process even if production
catches the denial. Report the stable diagnostic code `PDD_TEST_ACCOUNT_HOME`,
without account data. Tests of account-home fallback must inject their userInfo
port. Cover both a direct lookup and a production caller that catches the error.

Load isolation before production code in focused test entrypoints or their
shared fixtures. The npm test command also preloads isolation, so a new test gets
a temporary HOME even if it omits the shared import. Each process owns its home;
parallel test files cannot remove another file's home.
Each isolated process also sets a private `PDD_INTERPRETER_QUEUE` under its
allocated temporary home, replacing inherited selectors. Checks using a fresh
injected environment or a native child must explicitly carry a fixture queue.
The shared runtime ports fixture supplies that queue when absent, including after
environment replacement. Workspace-evidence and workflow step-result fixtures supply private queue selectors in their fresh environments. Repair-ceiling fixtures retain the private selector when they narrow their environment to HOME. Exercise those public fixture consumers with the machine-queue guard still active. Never use the machine default interpreter queue in tests.
Extend the leak guard to queue access: reject reads and writes to the default
`/tmp/pdd-interpreter-UID` path or its children before I/O, with diagnostic
`PDD_TEST_INTERPRETER_QUEUE`. Fail the owning test process even when the error is
caught. Cover synchronous, callback and promise filesystem access, and renames
into the queue. A synthetic caller queue must keep the same entries and bytes
after real fake-runtime checks and native children. Also cover the npm preload
without an explicit helper import and cleanup on success and failure. Remove only the allocated
temporary directory when its owning process exits. Do not add a dependency.

The regression guard runs real fixture tests with a synthetic caller home and
synthetic state/config/skill directories. Those caller directories must keep the
same entries and bytes. Exercise the metrics selector/composition and the outage
fixture environment replacement paths using their existing external fakes.
A consumer of the shared workspace fixture must also keep default workflow
state out of the caller HOME. The fixture's private home must leave `<parent>/home`
available for consumers to create their own home. Both the fixture environment
and a consumer's HOME override must select default state within their respective
homes. Preserve the MCP pending, owned and aborted ownership cases and their
supplied-state selection checks.
A control using the old leaking fixture must fail the unchanged caller-home
expectation. Also exercise default state and skill writes, a child process and a
missing injected HOME inside the isolated process. Run the actual npm test script in a synthetic
checkout with a new test that omits the import, and check the same caller-home boundary. Cleanup must leave
no owned test home after an ordinary success or test failure.

The named launcher, runtime-slots and product saved-checks regressions must
also work under a synthetic agent caller. Launcher fixtures explicitly mask an
absent CODEX_HOME at the injected launcher boundary, including later ticks.
Concurrent native runtime fixtures use a private interpreter queue and a real
clock with real asynchronous waits for native filesystem locks; a rapidly
advancing shared fake clock cannot stand in for elapsed lock time. Construct
these fixture environments explicitly so caller job limits, queue selectors and
agent settings cannot affect their results. The slots fake must answer a GET
before POST registration with HTTP 404, like the service, and retain its unique
POST, capacity, wait barrier and completion checks. Exercise this order directly.
VM suite command fakes keep their scenario paths in the fake executable itself,
not in inherited environment variables. Affinity regressions check the clean
child environment and reserved CPU list together.
Keep the health transport's asynchronous shutdown marker and bounded observation
from #3089. Do not import operational captures as fixtures.

## Dependencies

- [Workflow state](../cli/workflow-runs.prompt.md), [interpreter client](../cli/runtime-client.prompt.md), [skills](../cli/skills-install.prompt.md) and [Herdr layout](../cli/workflow-herdr-layout.prompt.md): required path-selection context for authoring and native verification.
- [Prompting guide](../../docs/prompting-guide.md): required authoring context.

## Native boundary

This harness uses Node's filesystem, process environment and test runner. It has
no interpreter operation and makes no model or live service calls.

<details><summary>Runtime interface</summary>

```json
{"status":"approved","prose_sha256":"d04fabdd89db92b7db48d9482e29992959c4e7b729fc9fd56c21cf631902107e","entries":[],"calls":[],"resources":[],"limits":{"max_steps":1,"max_model_calls":1},"conventions":[]}
```

</details>
