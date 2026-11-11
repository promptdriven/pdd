# Declare the maps a shell Story seeds

As a prompt author, I want my pure shell Story to declare the app maps its screens use, so I can bind their resources without executing an unrelated tester warm-up.

Draft for person review. Expected results are proposed, not approved.

## Acceptance criteria

1. A pure shell Story can declare the app maps its screens use, so lint and a check accept map-only resource bindings without executing an unrelated tester warm-up.
2. The files preview, lint and check select each declared map, its dispatched prompts, their required dependencies and stylesheets; unrelated maps and tester prompts stay out of the upload.
3. A map declaration keeps existing safe-source, workspace and Story boundaries; a required missing or unsafe file refuses with the referring path instead of sending an incomplete upload.
4. Malformed map selections and unknown scenario keys remain refused; a declared map never makes a misspelled simulation operation valid.
5. An absent or empty app_maps selection keeps existing no-map behavior, and combined Story selection preserves each Story's own declared-map closure.

## Rules to check

A declaration selects required source. It does not execute extra operations or grant permission to read excluded files. Forbidden: accepting the key but omitting its map, adding warm-up steps, inferring undeclared maps, weakening source safety, or accepting a misspelled operation.

## Evidence and check limits

The existing preflight prompt is incomplete: it names caller `appMap` capture but not scenario `app_maps` capture. It has no executable Runtime interface. Its local interface draft is refused by an existing required-context cycle. There is no before prompt-check verdict or AI pass. The proposed cases below need native public-boundary tests in the code stage; they are not executable Runtime scenarios.

[Proposed synthetic native cases](../test/runtime-admission/runtime-declared-app-maps-cases.json). Runtime owns map validity and simulation-binding admission; the client owns complete safe source selection. The focused change adds no Runtime implementation or queue change.
