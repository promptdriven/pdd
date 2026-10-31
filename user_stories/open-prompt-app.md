# Open my whole app from its prompt

I can type `pdd main.prompt.md` and use the whole app, with no Story to prepare.

## Acceptance criteria

1. Opening a prompt that is a screen, or reaches a screen through calls or Dependencies, prints one URL for the whole reached app and says answers come from prompts, without claiming to test generated code.
2. The opened app retains every screen, navigation handler and tab in each reached app map, while unrelated app maps stay out.
3. Opening a prompt that reaches named HTTP routes serves those routes at localhost port 8080 without a Story; Ctrl-C closes the local listener and keeps program data.
4. Screen and HTTP runs keep the program's saved data, the supplied starting data or the empty fresh-start data, without replacing it with product seed values.
5. An app setup error explains the authored source to fix and a retry that keeps the entry, flags and product context; uncertain setup does not create a second session.
6. App source is captured through the ordinary safe dependency pipeline without a synthetic Story or test, a separate archive or changes to authored files.

## Rules to check

Forbidden results include a partial tab map, uploading unrelated Stories, printing a second Screen URL, routing to guessed HTTP entries, or resetting saved data during recovery. HTTP security and headers remain governed by the existing server contract.

## Native verification boundary

Runtime check: NOT REPLAYED; native source capture, session adapters, localhost listeners and terminal output are not bound to interpreter observations. Replay the requirement cases against real module boundaries with fake transport and file bytes. A fake response does not prove the hosted Screen or runtime no-Story admission. Pocket tab navigation and curl against staging require separate live evidence.
