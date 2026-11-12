# Gemini shell safety

As a person using a Gemini workflow, I can learn before relying on it that shell safety dialogs can stop unattended work, and see that dialog named in status when it appears.

## Acceptance criteria

1. Starting a Gemini workflow warns that shell safety dialogs can override `--yolo` and need a person even unattended.
2. When a running Gemini chat is blocked on the shell safety dialog, detail, list and JSON status name it and direct me to the chat without answering it.
3. An unrelated or unreadable blocked dialog retains the generic status.

## Rules to check

- The live ordered shell safety menu is named when either choice is selected, with or without its selection footer.
- An older menu followed by an input or a different dialog, or an unreadable screen, keeps the generic blocked status.
- Status reads the pane without answering the dialog.
