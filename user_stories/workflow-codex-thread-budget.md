# Workflow Codex thread budget

I can give the Codex chats pdd starts enough room for independent helpers while keeping my own configuration and seeing which limit was selected.

## Acceptance criteria

1. I can start a bundled Codex workflow with 5 total thread slots for bug/feature story and prompt-pr or small-change plan, and 6 for bug/feature code or small-change build, when no explicit personal value exists.
2. My explicit modern Codex thread setting takes precedence over either agents alias, and either alias counts helpers plus one main thread; my value is preserved even below the workflow request or above 8.
3. I can opt a custom area into an integer thread budget from 4 through 8; invalid supplied budgets are rejected, while an area without the field keeps its existing launch behavior without reading configuration.
4. If configuration or its active layers cannot be established safely, my chat starts without a thread override and its record and status visibly explain the unknown setting.
5. First starts, stopped-session resumes and requested fresh sessions use the saved account configuration, preserve newly changed explicit personal settings, and retain the selected total and source in chat/run records; status reports saved launch facts without rereading configuration.
6. Claude chats and legacy saved areas keep their existing behavior; thread policy changes neither approval authority nor checker independence, and an exhausted checker still reports "Not checked:" honestly.

## Rules to check

The workflow cap applies to workflow declarations, never personal values. Unknown configuration must never be treated as no explicit value. Saved areas without a budget must not acquire new bundled defaults. Config files remain untouched; no credentials are read.
