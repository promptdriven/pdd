<!-- pdd-story-prompts: prompts/<module>_<language>.prompt -->

# User Story: <name>

## Story

As a <persona>,
I want <behavior>,
so that <value>.

<!--
This file is the HUMAN-VERIFIED user story, and the source of truth. It holds
ONLY the one-sentence Story above — keep it plain and durable:
  - describe the user's stable goal and what they can do/see;
  - no flags, exit codes, or internals (those go in the contract);
  - never pin it to a specific external product/tool/UI ("like Claude Code's
    UI") or a time-/version-sensitive fact, so it survives the ecosystem
    changing.

The machine-checkable contract (acceptance criteria, oracle, candidate prompts)
is generated FROM this Story plus the issue and lives in a separate file:
  user_stories/contracts/<name>.contract.md
If you edit this Story, re-align the contract with the sync_user_story_contract()
library function in pdd/user_story_tests.py. There is no `pdd sync` user-story
command on this branch — `pdd sync` handles prompt code/test/example/contract
sync, not story contracts. Do not hand-edit the contract; but do review the
generated contract for false or over-broad oracle claims before relying on it,
since it is the actual oracle used by `pdd detect --stories` and `pdd fix`.
-->
