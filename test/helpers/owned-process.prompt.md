# Proof review fixture process ownership

Own `test/helpers/owned-process.mjs`, a test-only helper for the INTERRUPT and RECOVERY proof review fixtures. Its caller starts an owned proof runner and immediately establishes guaranteed cleanup before any subsequent fixture setup can throw. The helper must retain ownership independently of the fixture's PID or readiness file, from the moment it starts a process. Cleanup must stop and wait for the runner and all processes started by its proof command, including same-group descendants after the proof group leader exits, before it completes. Cleanup is safe to invoke after the runner has already exited and more than once. It must not signal the test runner or unrelated processes.

Export `spawnOwned(script, options = {})`, returning `{child, ended, cleanup}`. `script` is the Node module source for the proof runner, and `options` supplies spawn options; the helper owns its stdio channels. `child` is the spawned runner and `ended` resolves to `{code, signal}` when it closes. `cleanup()` returns a promise for termination and can be called repeatedly. A unique unpredictable ownership token is present in the runner’s initial environment and inherited by the fixture’s proof processes. Cleanup identifies exact token entries in Linux process environments, stops the runner and token-bearing processes before terminating them individually with process identity checks, and verifies their termination. This contract covers the proof review fixtures’ inherited environment and process structure; processes that remove the token are outside its scope.

The guarantee applies whether post-spawn fixture setup fails, the test succeeds, an assertion throws, the PID file is absent, empty, incomplete or malformed, or readiness times out. A PID file may report test observations but is not the sole authority for cleanup. The setup-failure regression must independently own and terminate its nested test and descendants even if observation publication fails, and wait for the nested test to exit. The fixture must still exercise its existing interruption and recovery assertions. Process ownership is limited to the processes started by that fixture; it does not change `proveRun`'s product contract.

## Dependencies

Linux process and signal facilities are required to start, identify, terminate and wait for real processes and their descendants.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"","kind":"native-only","reason":"Real operating-system process creation, same-group descendant ownership, signal delivery and termination cannot be established by bound Runtime ports."}
```

</details>
