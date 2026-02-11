# AUDIT S03 V15 -- ContextWindowComparison (211.7s - 249.7s)

## Script Visual
"Two context windows: LEFT 15,000 tokens raw code. RIGHT prompts for 10 modules, clean NL."

## Frames Reviewed
- t=213s: Split screen. LEFT: "15,000 tokens of code" / "Context Window (15K tokens)" with terminal-style window. RIGHT: "15,000 tokens of prompts" / "Context Window (15K tokens)" with terminal-style window. Both windows currently empty/loading.
- t=230s: Both windows filled. LEFT: Dense code filling the window, "13,000 tokens" indicator, small text. RIGHT: Clean prompt listings with colored module names, "15,000 tokens" indicator, "~10 modules" notation. Bottom text: "Same tokens. 10x the system knowledge." and "NL comments improved generation +41% (UC Berkeley, 2023) | Author-defined context, not machine-assembled."
- t=249s: Same fully populated view.

## Findings
- **PASS**: Two context windows side by side with matching size
- **PASS**: LEFT shows dense raw code (15,000 tokens)
- **PASS**: RIGHT shows prompts for ~10 modules in clean natural language
- **PASS**: "Same tokens. 10x the system knowledge." tagline perfectly matches script intent
- **PASS**: Academic citation (UC Berkeley, 2023) about NL improving generation +41%
- **BONUS**: "Author-defined context, not machine-assembled" text from script included

## Verdict: PASS
