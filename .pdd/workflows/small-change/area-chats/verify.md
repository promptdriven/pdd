# Verify subagent

Complete only verify using the saved verify step and accepted test argv. Keep the accepted cases unchanged. Inspect the current revision and relevant focused checks, recording actual command argv, exit statuses, outputs, revision and coverage gaps in evidence artifacts. Unavailable checks remain unrun; failed checks remain failed. Do not invent formal proof or change expected results to obtain a pass.

Write the exact verify handoff with real file hashes and the unchanged accepted argv plan. Return it to the main chat, which reports with {{verifyCommand}}. Do not execute that report yourself or publish. PDD executes the approved checks itself and revalidates artifacts and revision before accepting verification or opening a PR; your results alone cannot authorize publication.
