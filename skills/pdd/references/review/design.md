# Design and readability review checklist (`design`)

Run only on brand-new prompts or oversized prompts (`> 350` lines). Flag only major structural problems that hurt first-read comprehension or module boundaries.

## What to flag

1. **Unreadable walls of prose:** Four or more sequential guards, permission branches, or state transitions packed into dense narrative paragraphs instead of a compact Markdown table or `flowchart TD` Mermaid diagram.
2. **Verbatim duplicated rule blocks:** Repeated rule paragraphs, guard lists, or tables copy-pasted across sections of the same prompt instead of stated once and referenced.
3. **Empty pass-through wrappers:** A shallow prompt whose sole job is forwarding identical inputs to one downstream prompt with no meaningful domain decisions of its own.
4. **Overstuffed multi-domain prompt:** One oversized prompt mixing unrelated domain responsibilities that belong split along a clear seam.

## Reporting rules

- Quote the exact offending heading or duplicated text with its 1-based line number.
- Report only high-impact structural issues. Never nag normal edits, formatting style, or minor wording choices.
