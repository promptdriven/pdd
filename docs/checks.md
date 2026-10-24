# What checks mean

PDD Alpha helps author contracts and expected cases. Its local issue runner can launch native agent stages and execute approved project test commands. It does not provide a prompt execution Runtime, standalone PDD lint, hosted CHECK or PDD Try session.

For the included synthetic code example, from the repository root:

```sh
node --test examples/ticket-status/test/status.test.mjs
```

That native Node test compares actual implementation behavior with independently authored cases. The cases' JSON shape belongs to this example, not a general Runtime schema. Review the prompt and Story as well as the tests. Passing these cases is useful evidence, not exhaustive correctness or formal proof.

For a different project, inspect its instructions and use its actual test runner. Keep the intended behavior and expected results independent of the implementation's output. Report failures without silently changing expectations to make them pass. A test that was only written is unrun.

The public repository's full suite is `npm test`. Package checks should verify that the CLI works from a clean extracted archive and that guide, skill, recipes and example links resolve without private services. A command's help entry alone is not behavioral acceptance. Capturing Herdr/native/GitHub stand-ins do not establish actual installed-agent, attachment or PR behavior. Two isolated issues can exercise worktree boundaries without proving capacity for 20–30 simultaneous native sessions. Removing a repository cap does not establish machine capacity; report actual platform and session results. See [CONTRIBUTING.md](../CONTRIBUTING.md).

An agent's review, project tests, manual app observations and optional formal analysis are different forms of evidence. Report what actually happened, with the scope and remaining uncertainty. Do not require an unavailable Runtime lint command before calling a reviewed draft ready for its next agreed step.
