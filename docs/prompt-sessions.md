# Prompt sessions

A PDD session helps make the behavior contract clear before changing code. Start with the task and the affected behavior. The session should inspect the repository's instructions, locate the owning prompt and relevant public interface, and ask only about decisions that the available evidence cannot settle.

For prompt work, read the [Prompting guide](prompting-guide.md), update the canonical prompt and Story, and check the result using commands supported by `pdd --help`. Keep expected examples authored and reviewable. A check result describes the prompt evaluation it actually performed; it does not establish that generated code is correct.

The session may offer a Try when a person can learn from exercising the proposed behavior. Try is optional and depends on the installed release. A person reviews and approves the current prompt and Story revision. The feature and bug recipes use `approval: story`, `publish-prompt-pr`, and `wait-for-merge: pr1` to pause for approval, publish the Prompt PR, and hold code work until the person merges it. The code change is tested at its public boundary; `publish-code-pr` and `wait-for-merge: pr2` publish its Code PR and hold completion until the person merges the current revision. These workflow actions depend on support in the installed release.

If the request is a small, contained change that does not need prompt adoption, use the [small-change workflow](../.pdd/workflows/small-change/WORKFLOW.md). It can put the code and its checks in one PR. If the change depends on a prompt rule, update that owning prompt first even within the same PR.

The built runtime is a separate package, free to use with PDD and not available for copying or resale. Its source is not in this repository. Sessions should report the installed release's actual support and keep unavailable runtime checks visible rather than promising a future result.
