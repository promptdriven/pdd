# Shared world
Owner: the plan run (changes go through a plan PR).

| Key | What it holds | Writer | Readers | How it is written |
|---|---|---|---|---|
| menu | Drinks, sizes and prices in cents | server | phone, server | Replace the menu. |
| orders | Customer orders and their status | server | phone, server | Add an order or update its status. |
| tickets | The barista's tickets | barista | server, barista | Add a forwarded ticket or mark it done. |
| order_requests | Requests from the phone | phone | server | Append a request. |

Each key has one writer. A refused order has a reason and creates no ticket.
A done ticket makes its order Ready. The phone does not write tickets.
