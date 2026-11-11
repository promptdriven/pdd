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

## Shared world records

These plan-owned records define the existing shared-world values; the writer table above remains authoritative.

### menu_entry
```json
{"type":"object","properties":{"drink":{"type":"string"},"size":{"type":"string"},"priceCents":{"type":"integer"}},"required":["drink","size","priceCents"],"additionalProperties":false}
```

### order
```json
{"type":"object","properties":{"id":{"type":"string"},"drink":{"type":"string"},"size":{"type":"string"},"status":{"type":"string","enum":["Ordered","Ready","Refused"]},"reason":{"oneOf":[{"type":"string"},{"type":"null"}]}},"required":["id","drink","size","status","reason"],"additionalProperties":false}
```

### order_request
```json
{"type":"object","properties":{"id":{"type":"string"},"drink":{"type":"string"},"size":{"type":"string"}},"required":["id","drink","size"],"additionalProperties":false}
```
