# Prompt sessions

A PDD session helps make the behavior contract clear before changing code. Start with the task and the affected behavior. The session should inspect the repository's instructions, locate the owning prompt and relevant public interface, and ask only about decisions that the available evidence cannot settle.

For prompt work, read the [Prompting guide](prompting-guide.md), update the canonical prompt and Story, and check the result using commands supported by `pdd --help`. Keep expected examples authored and reviewable. A check result describes the prompt evaluation it actually performed; it does not establish that generated code is correct.

The session may offer a Try when a person can learn from exercising the proposed behavior. Try is optional and depends on the installed release. A person reviews and approves the current prompt and Story revision. When prompts change, the session opens a Prompt PR; the person reviews and merges that PR before code implementation begins. The resulting code change is tested at its public boundary and submitted as a Code PR for review. The person decides whether to merge the current revision.

If the request is a small, contained change that does not need prompt adoption, use the [small-change workflow](../.pdd/workflows/small-change/WORKFLOW.md). It can put the code and its checks in one PR. If the change depends on a prompt rule, update that owning prompt first even within the same PR.

The built runtime is a separate package, free to use with PDD and not available for copying or resale. Its source is not in this repository. Sessions should report the installed release's actual support and keep unavailable runtime checks visible rather than promising a future result.
