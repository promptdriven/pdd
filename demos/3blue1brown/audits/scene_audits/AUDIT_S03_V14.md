# AUDIT S03 V14 -- PromptGovernsCode (203.5s - 210.4s)

## Script Visual
"Prompt glows. Small (10-15 lines) but governs 200-line file. Ratio: '1:5 to 1:10'"

## Frames Reviewed
- t=205s: Left side: "PROMPT" header with glowing blue box showing prompt text: "Parse user IDs from untrusted input.", "Return None on failure, never throw.", "Handle unicode.", "Strip whitespace.", "Validate alphanumeric.", "Log validation failures.", "Return cleaned string or None." Below: "~15 lines"
- t=210s: Split view. LEFT: Same prompt (~15 lines). RIGHT: "GENERATED CODE" header with full code file showing imports, class, function. "~200 lines" label. Arrow connecting prompt to code.

## Findings
- **PASS**: Prompt shown as ~15 lines of clean natural language
- **PASS**: Generated code shown as ~200 lines of Python
- **PASS**: Size contrast is dramatic and clear
- **MINOR**: The "1:5 to 1:10" ratio is not explicitly shown as text. Instead, "~15 lines" and "~200 lines" labels let viewers calculate the ratio. The intent is communicated effectively.
- **PASS**: Arrow connecting prompt to code emphasizes the governance relationship

## Verdict: PASS (ratio communicated via line counts rather than explicit "1:5 to 1:10" text)
