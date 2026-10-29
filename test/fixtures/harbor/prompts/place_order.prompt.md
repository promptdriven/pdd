# Place a Harbor Coffee order

Operation `place_order` turns a customer's order into a priced order.

The input has:
- `customerName`: the name for the order.
- `pickupAt`: the pickup time as the customer wrote it, for example "08:30".
- `items`: one or more order lines. Each line has `itemId`, `size` ("S", "M" or "L")
  and `quantity` (1 to 20).

Use this menu. Prices are in whole cents.

| itemId | name | S | M | L |
|---|---|---|---|---|
| espresso | Espresso | 275 | 325 | 375 |
| drip | Drip Coffee | 210 | 245 | 280 |
| latte | Latte | 395 | 445 | 495 |
| cappuccino | Cappuccino | 385 | 435 | 485 |
| cold-brew | Cold Brew | 360 | 410 | 460 |
| matcha | Matcha Latte | 420 | 470 | 520 |
| croissant | Butter Croissant | 315 | 395 | 475 |
| muffin | Blueberry Muffin | 250 | 295 | 350 |

Return the order:
- `customerName` and `pickupAt`, copied from the input with no change.
- `items`: one line for each input line, in the same order. Each line has `itemId`,
  `name` (from the menu), `size`, `quantity`, `unitPriceCents` (the menu price for that
  size) and `lineTotalCents` (`unitPriceCents` times `quantity`).
- `totalCents`: the sum of all `lineTotalCents`, in whole cents.

If an `itemId` is not on the menu, return the error `unknown-item`.
There are no external resources, operating-system commands, or persistent state.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{
  "status": "approved",
  "prose_sha256": "d5958a8577dcb8dd6ff25c8df4ea3b85e8c5dcf7c16863d8e502a24095db6abb",
  "entries": [
    {
      "operation": "place_order",
      "input_schema": {
        "type": "object",
        "properties": {
          "customerName": {"type": "string", "minLength": 1},
          "pickupAt": {"type": "string", "minLength": 1},
          "items": {
            "type": "array",
            "minItems": 1,
            "items": {
              "type": "object",
              "properties": {
                "itemId": {"type": "string"},
                "size": {"type": "string", "enum": ["S", "M", "L"]},
                "quantity": {"type": "integer", "minimum": 1, "maximum": 20}
              },
              "required": ["itemId", "size", "quantity"],
              "additionalProperties": false
            }
          }
        },
        "required": ["customerName", "pickupAt", "items"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "customerName": {"type": "string"},
          "pickupAt": {"type": "string"},
          "items": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "itemId": {"type": "string"},
                "name": {"type": "string"},
                "size": {"type": "string", "enum": ["S", "M", "L"]},
                "quantity": {"type": "integer"},
                "unitPriceCents": {"type": "integer"},
                "lineTotalCents": {"type": "integer"}
              },
              "required": ["itemId", "name", "size", "quantity", "unitPriceCents", "lineTotalCents"],
              "additionalProperties": false
            }
          },
          "totalCents": {"type": "integer"}
        },
        "required": ["customerName", "pickupAt", "items", "totalCents"],
        "additionalProperties": false
      },
      "errors": ["unknown-item"]
    }
  ],
  "calls": [],
  "resources": [],
  "limits": {"max_steps": 4, "max_model_calls": 2},
  "conventions": []
}
```
</details>
