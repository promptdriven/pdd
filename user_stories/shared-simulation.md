# Share simulation bindings

As a developer writing scenario tests, I want to share simulation bindings between scenarios, so that I maintain each binding once.

## Acceptance criteria

1. Two scenarios can use the same shared bindings and each receives the shared read and write bindings.
2. A scenario can replace a shared binding while retaining the other shared bindings.
3. A missing shared binding file is refused.

## Rules to check

- A scenario binding replaces the entire shared binding with the same identifier. Forbidden: combining fields from both bindings.
- Existing step overrides keep their precedence after expansion. Missing resource-operation bindings are still refused.
- Reference cycles, malformed references and unsafe targets are refused with the scenario and reference location; binding contents stay literal and shared files are not changed.
