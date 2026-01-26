# PDD Prompt Report: `prompts/customer_service_agent.txt`

## Score: 75/100

### Summary
Moderate quality prompt. Critical modularity issue detected.

### Issues
| Rule | Severity | Line | Description |
|---|---|---|---|
| MOD001 | error | 15 | Prompt exceeds 500 tokens without sub-prompt division. |
| SEC002 | warning | 42 | Potential PII placeholder detected: {{user_email}}. |
| STY005 | info | 1 | Consider adding a version tag to the header. |

### AI Analysis
The prompt is generally well-structured but lacks specific persona definitions.