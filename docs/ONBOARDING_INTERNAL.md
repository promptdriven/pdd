# PDD Internal Onboarding

For PDD employees with access to shared infrastructure.

> **Note**: This guide supplements the main [ONBOARDING.md](ONBOARDING.md). Complete steps 1-6 from that guide first, then return here for secrets management setup.

## Infisical Setup

PDD employees use Infisical for centralized secrets management instead of local `.env` files for API keys.

### 1. Accept the Invitation

Check your email for an Infisical invitation from the PDD team. Accept it and verify you can see the project in your Infisical dashboard.

### 2. Install the Infisical CLI

Choose the command for your operating system:

**macOS:**
```bash
brew install infisical
```

**Windows (PowerShell):**
```powershell
winget install infisical
```

**Linux:**
```bash
curl -1sLf 'https://artifacts-cli.infisical.com/setup.deb.sh' | sudo -E bash
```

### 3. Authenticate and Link Your Repository

From the root of the `pdd` repository:

```bash
# Log in to your Infisical account
infisical login

# Link your local repo to the Infisical project
infisical init
```

## Local Configuration

Even with Infisical, you need one local setting in your `.env` file:

```bash
# Add to .env (file path can't be stored in Infisical)
VERTEX_CREDENTIALS=/path/to/service-account.json
```

**To get the service account JSON:**
- Ask your team lead for access to the shared GCP service account, or
- Create your own following the Vertex AI setup steps in ONBOARDING.md

## Running Commands

Always use the `infisical run --` prefix to inject secrets:

```bash
# Run tests
infisical run -- make test

# Generate code
infisical run -- pdd generate module_name

# Sync a module
infisical run -- pdd sync module_name
```

## What's in Infisical

The following secrets are managed centrally:

| Category | Variables |
|----------|-----------|
| LLM API Keys | `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `GOOGLE_API_KEY`, etc. |
| Vertex AI | `VERTEX_PROJECT`, `VERTEX_LOCATION` |
| GCS Caching | `GCS_BUCKET_NAME`, `GCS_HMAC_ACCESS_KEY_ID`, `GCS_HMAC_SECRET_ACCESS_KEY` |

**Not in Infisical** (must be set locally):
- `VERTEX_CREDENTIALS` - path to your local service account JSON file
- `PDD_PATH` - path to your local PDD installation

## Troubleshooting

**"Secret not found" errors:**
- Ensure you ran `infisical init` in the repo root
- Verify you have access to the project in your Infisical dashboard

**"API key appears too short" warnings:**
- This usually means Infisical secrets aren't being loaded
- Check that you're using `infisical run --` prefix

**Conflicts with local `.env`:**
- Infisical values take precedence over `.env` when there's a name conflict
- Keep only `VERTEX_CREDENTIALS` and `PDD_PATH` in your local `.env`

## Cost-Efficient CLI Usage

PDD has Google Cloud credits and limited Claude Max seats. Use AI CLI tools in this order to maximize value:

| Tier | Model | CLI Tool | Cost |
|------|-------|----------|------|
| 1st | Gemini Flash 3.0 | Gemini CLI | Free (GCP credits) |
| 2nd | Gemini Pro 3.0 | Gemini CLI | Free (GCP credits) |
| 3rd | Claude Opus 4.5 | Claude Code CLI | Limited (Max subscription) |

### Try and Escalate

1. **Start with Gemini Flash 3.0** for all tasks
2. **Escalate to Gemini Pro 3.0** if Flash struggles or produces poor results
3. **Use Claude Opus 4.5** only for truly complex problems that Gemini can't handle

This approach leverages our GCP credits while conserving limited Claude Max usage for when it's really needed.

## PDD Module Development Workflows

PDD has different workflows for **bug fixes** vs **new features**. The key principle: *bug fixes start with tests; features start with prompts*.

### Bug Fix vs Feature: Which Workflow?

| Task Type | Start With | Why |
|-----------|------------|-----|
| **Bug Fix** | Test file | Bugs represent *missed intent*—capture as a failing test first |
| **New Feature** | Prompt | Features represent *new intent*—define in the prompt first |

---

### Bug Fix Workflow

```mermaid
flowchart TD
    A[Bug reported] --> B[Create GitHub issue]
    B --> C[Write failing test]
    C --> D{Test fails?}

    D -->|No| E[Fix test - AI may have mocked it]
    E --> C
    D -->|Yes| F{Need prompt clarification?}

    F -->|Yes| G[Update prompt]
    G --> H[pdd fix module_name]
    F -->|No| H

    H --> I{Tests pass?}

    I -->|No, after retries| J{Can pdd fix solve it?}
    J -->|No| K[Manual fix or new issue]
    K --> H
    J -->|Yes| H

    I -->|Yes| L{Code changed, not just test?}
    L -->|No| M[AI cheated - fix test or prompt]
    M --> H
    L -->|Yes| N[pdd sync module_name]

    N --> O[Manual verification]
    O --> P{Actually works?}
    P -->|No| M
    P -->|Yes| Q[pdd update module_name]
    Q --> R[Update GitHub issue]
    R --> S[Create PR]
```

#### Steps

1. **Create GitHub issue** (enables parallel debugging):
   ```bash
   # Have Claude Code summarize the bug and create an issue
   # This lets you farm out multiple bugs to debug in parallel
   ```

2. **Write a failing test** (manually or via Claude Code):
   ```bash
   # NOTE: `pdd bug` doesn't work reliably yet - write tests manually
   # Add test to tests/test_module_name.py

   # Run the test to confirm it FAILS
   infisical run -- pytest -vv tests/test_module_name.py::test_specific_bug
   ```

   > **Why must it fail?** AI loves to mock things. If the test passes immediately, it's probably mocked up and not actually testing anything. A failing test proves you've pinpointed the real issue.

3. **Clarify the prompt** (if the bug reveals ambiguity):
   ```bash
   # Only if the prompt conflicts with expected behavior
   # Edit prompts/module_name.prompt directly
   # This is important because pdd fix reads the prompt
   ```

4. **Fix the code**:
   ```bash
   infisical run -- pdd fix module_name
   ```

5. **Verify the fix is real** (critical step!):
   ```bash
   # Check that CODE changed, not just the test
   git diff

   # If only the test changed and it passes - AI cheated!
   # The AI tends to do the easiest thing, which is often
   # modifying the test to pass rather than fixing the code
   ```

6. **Sync to regenerate example**:
   ```bash
   # Sync regenerates code and example (bug fix may add new inputs/outputs)
   infisical run -- pdd sync module_name
   ```

7. **Manual verification ("touch grass")**:
   ```bash
   # Run the actual command end-to-end
   # AI often works around problems rather than fixing them
   # You need to verify it actually works in reality
   ```

8. **Check if prompt needs updating**:
   ```bash
   # Run pdd update to see if prompt should change
   # Usually not needed for bug fixes, but check anyway
   infisical run -- pdd update module_name
   ```

9. **Update the GitHub issue and create PR**:
   ```bash
   # Have Claude Code:
   # 1. Summarize what was done
   # 2. Update the GitHub issue with findings
   # 3. Create PR linked to the issue
   ```

#### What if `pdd fix` can't fix it?

If `pdd fix` fails repeatedly even with agentic mode:
1. Analyze the scenario (multi-module issue? import problem?)
2. Try manual intervention
3. Create a new issue - it's likely a bug in `pdd fix` itself

---

### New Feature / Module Update Workflow

For adding features or maintaining modules, follow this workflow from the team discussion:

```mermaid
flowchart TD
    A[Feature request] --> B[Identify all affected modules]
    B --> C[pdd update on ALL modules]
    C --> D[pdd test until coverage >= 80%]
    D --> E{Coverage >= 80%?}

    E -->|No, keep trying| D
    E -->|No, unreachable| E2[Document justification + get approval]
    E2 --> F
    E -->|Yes| F[pdd fix --auto-submit for grounding]

    F --> G[Sync related docs: API, architecture]
    G --> H[Update prompts with new requirements]
    H --> I[pdd sync on all modules]

    I --> J[Run tests]
    J --> K{Tests pass?}

    K -->|No| L[pdd fix module_name]
    L --> I

    K -->|Yes| M[Write new tests for feature]
    M --> N[Manual verification]
    N --> O[Create PR]
```

#### Why This Order Matters

The preparation phase ensures:
- **Grounding**: Uploading existing code to PDD cloud means regenerations are grounded in proven patterns, not random
- **Prompt sync**: Prompts often drift from code; syncing first prevents conflicts
- **Test coverage**: Higher coverage = more reliable regeneration (the mold has more walls)
- **Document sync**: API docs define interfaces; including them in prompts ensures consistency across CLI and cloud

> **Critical**: Never update prompts with new requirements before syncing existing prompts to current code. Prompts that are out of sync with code produce unreliable regenerations.

#### Steps

1. **Identify affected modules** - List all modules that will change for this feature:
   - Check `docs/python_architecture.csv` for module dependencies
   - Search for imports of the modules you're changing
   - Look at which tests exercise the feature area

2. **Sync existing prompts** to current code state:
   ```bash
   # For EACH affected module
   infisical run -- pdd update module_name
   ```

3. **Increase test coverage** to at least 80%:
   ```bash
   infisical run -- pdd test module_name
   infisical run -- make coverage
   ```
   > High coverage = more mold walls = more reliable regeneration.

   **If 80% is unreachable:** Document why in the PR (e.g., external APIs, integration code) and get explicit approval before proceeding. Consider refactoring to improve testability.

4. **Upload to PDD cloud** for grounding:
   ```bash
   # --auto-submit uploads to vector database when tests pass
   infisical run -- pdd fix module_name --auto-submit
   ```
   > This ensures regeneration is grounded in proven patterns, not random.

5. **Sync related documents** (API docs, architecture files):
   - Update `docs/api.md` if interfaces change (required for CLI/cloud consistency)
   - Update `docs/python_architecture.csv` if module structure changes
   - Consider adding `<include>` tags in prompts to reference API docs

6. **Update prompts with new requirements**:
   ```bash
   # Edit prompts directly OR use pdd update interactively
   # Spend quality time here - prompts are the source of truth
   ```

7. **Regenerate all affected modules**:
   ```bash
   infisical run -- pdd sync module_name
   ```

8. **Fix any failures** and iterate:
   ```bash
   infisical run -- pdd fix module_name
   ```

9. **Write new tests** for the feature (using Claude Code or manually)

10. **Manual verification** - Touch grass, verify end-to-end

11. **Create PR** with test, prompt changes, and regenerated code

> **Note**: Modules with <50% coverage produce unreliable regenerations. Target 80% for reliable generation.

---

### PR Requirements Checklist

Before merging a PR, ensure it contains:

| Required | Item | Notes |
|----------|------|-------|
| ✅ | **Test** | Immediate rejection if missing - proves the bug existed |
| ✅ | **"All regression passed"** | So reviewer knows it's safe to merge |
| ⚠️ | **Prompt change** | Or comment: "prompt update not needed" |
| ⚠️ | **Example regenerated** | If prompt changed, example likely needs regeneration |
| ✅ | **Linked to issue** | PR and issue should reference each other |

---

### Quick Reference

| Command | Purpose | When to Use |
|---------|---------|-------------|
| `pdd fix` | Fix code to pass failing tests | Bug fixes, feature iteration |
| `pdd update` | Check if prompt needs changes | After fix, before PR |
| `pdd test` | Generate tests to increase coverage | Before regeneration (target: 80%) |
| `pdd sync` | Regenerate code, example & update few-shot DB | After fixes succeed |

> **Note**: `pdd bug` doesn't work reliably yet. Write tests manually or with Claude Code.

### Important Notes

- **Tests are permanent, code is ephemeral**: Tests accumulate over time; code is regenerated
- **Verify AI didn't cheat**: After `pdd fix`, check that CODE changed, not just the test
- **Touch grass**: Always manually verify the fix actually works end-to-end
- **Parallel debugging**: Create GitHub issues so multiple bugs can be debugged simultaneously
- **Few-shot learning**: Each successful sync updates the few-shot database, improving future generations
- **Coverage matters**: Modules with <50% coverage produce unreliable regenerations; target 80% for reliable generation
