# Working on PDD

Prompts are the source. Change the owning prompt before changing behavior in code. Keep one canonical prompt per public module. Use observable stories and independent expected results to check changes.

Use plain English in help and documentation. The public command is `pdd`. The guide is named “Prompting guide”. A terminal command shows the web app link or QR code; the person opens PDD on their own phone.

Keep this repository's source public under MIT. The phone app, Coordinator/server, billing, account pool, execution runtime, operations tools and internal fixtures remain outside this source tree. Workbench and Herdr source are deferred. The Host source follows once its excluded dependencies are separated; an installed built Host is a separate component.

Work on a topic branch. Preserve existing work. Never commit or push directly to main, force-push or enable auto-merge. A draft PR does not authorize merge. Merge requires review, passing required checks and approval of the current revision by the person responsible for the change.

Use focused local tests for the public client. Full product suites require an authorized runner. Do not run model calls, live service actions, installation, account sign-in/out or paid work merely to test a source change. Never print or commit credentials.

Keep reports and execution evidence outside the product repository. Include scope, checks, limitations, rollback and added/removed line counts in the PR description.
