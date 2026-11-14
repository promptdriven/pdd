# Check controls in their own screen views

As a screen author, I want local SVG layout lint to check each tab's controls against its own drawings, so that shared navigation stays checked without warnings for controls on other tabs.

## Acceptance criteria

1. Running `pdd lint --local` with Now, Agents, Workflows and Machines drawings and all shared and tab-specific controls present produces no SVG control warnings.
2. Running `pdd lint --local` when the shared tab-now button is missing from the Agents drawing warns for tab-now on Agents only.
3. Running `pdd lint --local` when Approve is missing from its Now drawing warns for Approve on Now only.
4. Running `pdd lint --local` with one linked drawing still warns for every declared control missing from that drawing.

## What must not change

- Warnings stay advisory and local lint makes no authentication, network or model calls.
- Drawing label, region, visibility, safety and workspace checks keep their existing behavior.

## Rules to check

- A shared missing control is reported on every drawing that omits it; a view-specific missing control is reported only on drawings in its scope. Forbidden: cross-view warnings or suppressing an own-view/shared omission.
- Section, list-item and labeled-block scopes end at their Markdown boundaries. Forbidden: a previous view absorbing a later view or shared controls.

```pdd-boundary
prompts/cli/svg-layout.prompt.md
```
