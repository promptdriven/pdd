# PDD Cloud API Documentation

This file is a stable prompt include for cloud endpoint names used by generated
PDD modules. Endpoint URL resolution is implemented by `pdd.core.cloud.CloudConfig`.

## Cloud Endpoint Contract

- `llmInvoke`: unified LLM invocation endpoint used by `llm_invoke` cloud mode.
- `generateCode`: remote code generation.
- `generateExample`: remote example generation.
- `generateTest`: remote test generation.
- `generateBugTest`: remote bug-test generation.
- `fixCode`: remote code/test repair.
- `crashCode`: remote crash repair.
- `verifyCode`: remote verification.
- `syncState`: remote sync state coordination.
- `trackUsage`: usage and cost tracking.
- `getCreditBalance`: credit-balance lookup.
- `submitExample`: example submission.

## Request Rules

- Build endpoint URLs through `CloudConfig.get_endpoint_url(name)`.
- Authenticate cloud requests with a JWT from `CloudConfig.get_jwt_token(...)`.
- Use `get_cloud_request_timeout()` for `requests` timeouts.
- Do not hardcode base URLs or timeout literals in generated modules.
