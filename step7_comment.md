## Step 7: Prompt Classification

**Classification:** Code Bug

DEFECT_TYPE: code

### Analysis
The `auto-heal.yml` workflow unconditionally checked collaborator status via the `gh api`, which fails for the `prompt-driven-github[bot]` identity because GitHub Apps are not traditional collaborators. Since there is no explicit prompt specification file for the `.github/workflows/auto-heal.yml` CI workflow in this repository, this issue is classified as a code bug rather than a prompt defect. 

### Evidence
- **Prompt specifies:** (No explicit prompt file exists for this GitHub Action workflow)
- **Code implements:** Unconditionally queries the collaborators endpoint which returns a 404 Not Found for bot identities.
- **User expects:** The workflow to correctly authorize the bot identity so that bot-authored PRs can successfully pass the auto-heal checks and complete the autonomous loop.

### Conclusion
The workflow code did not account for bot identities. There is no prompt specification to fix, so this is classified as a code bug. Proceeding with test generation.

---
*Proceeding to Step 8: Test Plan*