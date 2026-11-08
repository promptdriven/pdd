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
parallel test files cannot remove another file's home. Remove only the allocated
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

## Dependencies

- [Workflow state](../cli/workflow-runs.prompt.md), [interpreter client](../cli/runtime-client.prompt.md), [skills](../cli/skills-install.prompt.md) and [Herdr layout](../cli/workflow-herdr-layout.prompt.md): required path-selection context for authoring and native verification.
- [Prompting guide](../../docs/prompting-guide.md): required authoring context.

## Native boundary

This harness uses Node's filesystem, process environment and test runner. It has
no interpreter operation and makes no model or live service calls.

<details><summary>Runtime interface</summary>

```json
{"status":"approved","prose_sha256":"66aa5f2392603c3432c73419f5cfba109f80030cb9471277468cf95c20efe14c","entries":[],"calls":[],"resources":[],"limits":{"max_steps":1,"max_model_calls":1},"conventions":[]}
```

</details>
