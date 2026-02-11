# AUDIT: S04 V4 -- LongPrompt

## Scene Info
- **Section:** Part 4 - The Precision Tradeoff
- **Component:** LongPrompt
- **Time Range:** 26.7s - 34.6s
- **Frames Reviewed:** t=27.5s, t=30.0s, t=33.5s

## Script Visual
> "Long detailed prompt: parser_v1.prompt - 50 lines."

## Observed Visual
- **t=27.5s:** A code/prompt panel appears against a dark navy background. Header bar reads "parser_v1.prompt" on the left and "51 lines" on the right (with "51 lines" also shown as a badge). The content shows structured sections:
  - "# User ID Parser - Version 1"
  - "## Purpose" with description text
  - "## Input Handling" with bullet points (Accept string input, Handle null/undefined, Handle empty strings, etc.)
  - "## Validation Rules" with bullet points (alphanumeric plus underscore, min/max length, case-insensitive, etc.)
  - "## Unicode Support" section beginning
  - Section headers are highlighted in orange/amber color
- **t=30.0s:** The prompt content has scrolled slightly, showing more sections:
  - "## Unicode Support" (Accept Unicode, Normalize to NFC, Handle combining characters)
  - "## Error Handling" (Never throw exceptions, Return None for invalid input)
  - Content continues to be dense and detailed
- **t=33.5s:** Further scrolling reveals additional sections:
  - "## Error Handling" (with more bullets: Log validation failures, Provide error context)
  - "## Edge Cases" (Single-character IDs, Numeric-only IDs, Empty after trimming -> None, Only special chars -> None)
  - "## Performance" (O(n) complexity maximum)
  - On the right side, 3 small orange "test" blocks have appeared, labeled "3 tests"

## Accuracy Assessment
| Criterion | Status | Notes |
|-----------|--------|-------|
| Long detailed prompt | PASS | Dense, multi-section prompt with extensive bullet points |
| File name: parser_v1.prompt | PASS | Clearly shown in the header bar |
| Line count: ~50 lines | PASS | Shows "51 lines" (close enough to the script's "50 lines") |
| Dense requirements visible | PASS | Multiple sections with detailed specifications are readable |
| Scrolling animation | PASS | Content scrolls to show full depth of the prompt |

## Overall Grade: PASS

## Notes
- The "51 lines" vs script's "50 lines" is a trivial discrepancy (likely due to an off-by-one in content generation). This is acceptable.
- The prompt content is impressively detailed and realistic -- it covers Input Handling, Validation Rules, Unicode Support, Error Handling, Edge Cases, and Performance. This effectively conveys "every single detail must be specified."
- The auto-scroll effect is good for showing the full depth without requiring the viewer to read every line.
- The small test blocks appearing at t=33.5s (showing "3 tests") provide a nice transition hint toward V5 (which will show many more tests).
- Color coding (orange section headers vs white text) improves readability.
