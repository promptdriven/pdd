# Coffee pickup: map
Sentence: "A phone app to order coffee, a shop server, and a barista screen."
Size: medium (12 CORE Stories, 3 parts)

## Parts
| Part | Folder | What it is |
|---|---|---|
| phone | prompts/phone | The app that a customer uses. |
| server | prompts/server | The shop server between the phone and the barista. |
| barista | prompts/barista | The screen behind the counter. |

## Stories
| Id | Part | Story | Tag |
|---|---|---|---|
| P01 | phone | I see the menu with prices. | CORE |
| P02 | phone | I order a latte and see "Ordered". | CORE |
| P03 | phone | I see "Ready" when my order is done. | CORE |
| P04 | phone | I see a reason when my order is refused. | CORE |
| S01 | server | My valid order becomes a ticket. | CORE |
| S02 | server | My order for an unknown drink is refused with a reason. | CORE |
| S03 | server | My completed ticket makes the order ready. | CORE |
| S04 | server | I can read the current status of my order. | CORE |
| B01 | barista | I see waiting tickets. | CORE |
| B02 | barista | I mark a ticket done. | CORE |
| B03 | barista | I see the drink and size on each ticket. | CORE |
| B04 | barista | I see when there are no waiting tickets. | CORE |
| P09 | phone | I can save a favourite drink. | LATER |

## Journeys
| Id | Journey | Stories |
|---|---|---|
| J1 | I order a latte. The barista sees it and marks it done. My phone shows "Ready". | P02, S01, S03, B01, B02, P03 |

## Questions
| Id | Question | Recommendation | Example | Answer |
|---|---|---|---|---|
| Q1 | Can a customer cancel an order? | No, not in the first version. | "Cancel" is LATER. | No. |
