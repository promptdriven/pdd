# Coffee pickup: plan

## Boundaries
| From | To | What crosses | Contract |
|---|---|---|---|
| phone | server | order_in, order_view | contracts/phone-server.md |
| server | barista | ticket, ticket_done | contracts/server-barista.md |
Never crosses: the phone never talks to the barista screen.

## Runs
| Run | Part | Slice | Stories | Needs |
|---|---|---|---|---|
| server-1 | server | 1 | S01, S02, S03, S04 | plan PR |
| phone-1 | phone | 1 | P01, P02, P03, P04 | plan PR |
| barista-1 | barista | 1 | B01, B02, B03, B04 | plan PR |
| journeys | all | 1 | J1 | server-1, phone-1, barista-1 |
