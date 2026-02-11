# AUDIT: S02 V13 -- PromptGeneratesCode

## Scene Info
- **Component**: PromptGeneratesCode
- **Time Range**: 155.2s - 177.0s
- **Frames Reviewed**: t=158s, t=166s, t=175s

## Script Visual
> "The Verilog code morphs into a glowing document labeled 'PROMPT'. The gate-level netlist morphs into lines of software code. The Synopsys verification checkmark morphs into a test suite with green checkmarks."
> "The prompt document pulses. Code flows out of it, filling a defined shape. Tests appear as walls around the code, constraining it."

## Observed Visual
Frame at t=158s: Upper-left: A glowing white document/panel labeled "PROMPT" in orange/red text. The prompt content reads:
- "Convert input to Python"
- "null values -> None"
- "Ensure valid UTF-8"
- "Return formatted str"
To the right, faint code-like lines are beginning to appear/flow outward from the prompt, representing generated code starting to materialize.

Frame at t=166s: The PROMPT document remains in the upper-left with its white glow. The generated code has now filled a large area of the screen, contained within an orange-bordered rectangle. Text labels around the code block act as constraints:
- Top: "null -> None"
- Left: "valid format required"
- Right: "handles unicode"
- Bottom: "no exceptions"
This represents the tests/constraints as walls surrounding the generated code.

Frame at t=175s: The PROMPT document is now smaller (upper-left corner), the generated code fills the center-right within its orange-bordered test constraint box. The labels (constraints/tests) surround the code as walls. Subtitle text: "The prompt is your mold. The code is just plastic. And just like chip synthesis--the code is different every generation. But the tests lock the behavior. The process is deterministic."

## Verdict: PASS

## Severity: N/A

## Notes
- Strong match to script. The PROMPT document is clearly labeled and glowing, code flows out of it, and tests appear as walls/constraints around the code.
- The orange-bordered constraint rectangle with labeled edges ("valid format required," "handles unicode," "no exceptions," "null -> None") effectively visualizes "Tests appear as walls around the code, constraining it."
- The morphing from Verilog -> PROMPT is implicit (the scene transitions rather than explicitly morphing), but the narrative continuity from V12's timeline makes this acceptable.
- The prompt content is realistic and specific (Python conversion task), adding credibility.
- The closing subtitle directly delivers the Part 2 thesis: "The prompt is your mold. The code is just plastic."
- This is the strongest visual payoff scene in Part 2, tying together all the analogies.
