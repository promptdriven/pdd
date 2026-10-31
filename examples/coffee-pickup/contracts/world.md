# Shared world
Owner: the plan run (changes go through a plan PR).

| Key | What it holds | Writer | Readers | How it is written | Schema |
|---|---|---|---|---|---|
| menu | Drinks, sizes and prices in cents | server | phone, server | Replace the menu. | `contracts/world.md#menu` |
| orders | Customer orders and their status | server | phone, server | Add an order or update its status. | `contracts/world.md#orders` |
| tickets | The barista's tickets | barista | server, barista | Add a forwarded ticket or mark it done. | `contracts/world.md#tickets` |
| order_requests | Requests from the phone | phone | server | Append a request. | `contracts/world.md#order_requests` |

Each key has one writer. A refused order has a reason and creates no ticket.
A done ticket makes its order Ready. The phone does not write tickets.

These illustrative schemas explicitly define the shared starting shapes.

### menu
```json
{"type":"array","items":{"type":"object","properties":{"drink":{"type":"string"},"size":{"type":"string"},"priceCents":{"type":"integer","minimum":0}},"required":["drink","size","priceCents"],"additionalProperties":false}}
```

### orders
```json
{"type":"array","items":{"$contract":"contracts/phone-server.md#order_view"}}
```

### tickets
```json
{"type":"array","items":{"$contract":"contracts/server-barista.md#ticket"}}
```

### order_requests
```json
{"type":"array","items":{"$contract":"contracts/phone-server.md#order_in"}}
```
