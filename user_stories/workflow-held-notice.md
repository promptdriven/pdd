# Know when a held PR 1 notice will not be sent

I can see when a held PR 1 notice will not be sent after my run moves to code, and read what it said and why it was held.

## Acceptance criteria

1. A PR 1 notice held by a dialog or an unreadable screen remains visible after the run moves to code. Each text status view that lists it says it was not sent and later changes will not send it. It shows the full saved text, including line breaks, and the last delivery reason.
2. The saved notice keeps its text, original chat, pending state and last reason. JSON status retains these saved facts. Reading status changes no delivery data.
3. A later changes command sends my new request to the code chat without the held notice. The notice adds no change round, question, gate or approval and does not advance the run.
4. While the original area is current, held notices still go first in order and send once. Notices that may already have been sent and sends still in progress stay protected. Held human requests keep their original chat and their existing answer, change and approval effects.

## Rules to check

- The final non-delivery result applies only to a definitely unsent pending pdd notice whose original area is no longer current. It must not claim that an uncertain or in-progress notice was never sent.
- Status preserves the saved notice and delivery data. It must not shorten the saved text, lose the last reason, mark the notice delivered or send it to another chat.
- A notice cannot approve or advance the run, change a question or gate, or add a change round. Delivery to the same chat keeps its order and cannot send one accepted notice twice.
