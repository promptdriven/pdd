# Contribute to PDD

Change the owning prompt before changing the behavior of a source module. Use a Story to say what a person needs and test vectors to give independent expected results. Keep the prompt, code and tests in the same reviewed change.

Use Node.js 22.16 or newer. Read `pdd --help` from your installed client for available commands. The public client checks use Node's built-in test runner. They do not need a model account or a live PDD service.

Open a topic branch and a draft PR. Explain what changed, why, which focused checks ran and what remains unproved. Include added and removed line counts. A maintainer and the responsible person review the current revision before merge.

This source is MIT licensed. The installed Host and execution runtime are separate packages. Do not add phone, server, runtime, billing, pool, operations or deferred Workbench implementation to this repository. Keep credentials and execution reports outside the source tree.
