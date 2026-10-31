# I get useful optional-step decisions

I can follow a feature or bug run without answering questions about steps that do not apply. When a step may help, PDD asks once, recommends what to do and explains its evidence. My agent passes that advice on unchanged.

## Acceptance criteria

1. For an explicitly scoped server change with no affected or planned screens, PDD records "skipped: no screen", continues to the Story step and does not ask about visual design.
2. For a change with two affected screens, PDD asks "Do you want a visual design step? yes/no" and says "Recommended: yes. This change has 2 screens."; a planned new screen counts before its files exist.
3. For a backend Story with a valid local simulation entry, PDD asks "Do you want to try it now? yes/no" and says "Recommended: yes. Story user_stories/api.md has a Simulator door.", gives `pdd simulate user_stories/api.md` and the hint "about 2 minutes", even without a screen or HTTP route.
4. When scope or evidence is missing, stale, malformed, unreadable or conflicting, PDD asks with "Recommended: yes" and an honest uncertainty reason; unrelated screens and filenames never establish this change's screen count or absence.
5. Repeating an unchanged pending decision does not ask twice and keeps the question visible while waiting; a genuine request for changes can produce a fresh decision, without approving anything or running a simulation.
6. PDD never skips try on the agent's advice, even when no runnable interface is known. It asks once in one line, accepts my "no" immediately without pushing, records exactly "skipped by the person" and continues without a try approval gate; this works in my own agent chat with no Herdr area chat or terminal, and a link from an earlier agent check does not make PDD ask again.
7. My no is recorded as a skipped step; my yes or an automatic skip never approves a gate, changes the workflow's step names or opens a PR by itself.
8. For another optional step, PDD asks with "Recommended: yes. PDD has no applicability rule for this optional step." rather than guessing whether it applies.
9. For a runnable CLI Story, PDD recommends yes and gives `pdd simulate user_stories/cli.md --cli --shell` with the hint "about 2 minutes".
10. For a runnable HTTP Story, PDD recommends yes and gives `pdd simulate user_stories/http.md --serve` with the hint "about 2 minutes".
11. For a runnable screen Story, PDD recommends yes and gives `pdd simulate user_stories/api.md` with the hint "about 2 minutes"; a screen takes precedence over API routes, and a sole CLI takes precedence over HTTP when there is no screen.

## Rules to check

Only an explicit, current, exhaustive no-screen declaration for this change, with complete and consistent local evidence, permits an automatic visual skip. Try never auto-skips: the agent must relay my current no/skip answer honestly, never invent it. An explicit "skipped by the person" relay of my answer is enough after the current question; it needs no extra terminal, Herdr chat or evidence gate. Other autonomous skipped reasons, stale answers and yes are insufficient. My agent may check with the simulation tools before the gate and give me the link or command, but never changes expected values itself. Unknown is never none. An existing screen must be linked to this change; a new planned screen needs an explicit declaration. A backend simulation needs no app map. A question waits for my answer, and repeating the same pending decision must not invent another question. A changed brief makes old declarations uncertain until refreshed. No optional-step decision supplies approval or permission to execute a simulation or publish a PR. The agent relays PDD's question and recommendation verbatim and does not invent advice.
