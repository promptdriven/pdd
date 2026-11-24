# Coffee pickup: server

Own only menu/orders. forward_tickets reads all four world keys. For each request without an order, create an order with its request id, drink and size: Ordered with null reason when menu contains drink/size; otherwise Refused with reason Unknown drink or size. Then mark any Ordered order whose corresponding ticket is done as Ready. Save orders only and return processed as number of newly created orders. Never remove requests and never write tickets. render returns server · Status HTML and orders. Do not call phone or barista operations.


Relational illustrative previews at 390 × 844; sample values come from the contracts and current world. The stacked arrangement applies at narrow and desktop widths with a readable content column.

![server status](../../views/server-status__stacked.ui.svg)

## Dependencies

- [Shared world](../../contracts/world.md): required generation/runtime context for shared records and single-writer ownership.
- [Phone/server contract](../../contracts/phone-server.md): required generation/runtime schema authority for order input.
- [Server/barista contract](../../contracts/server-barista.md): required generation/runtime schema authority for tickets and completion input.
- [Appearance](../../views/server-status__stacked.ui.svg)

Follow the linked stacked-card appearance: part heading, primary action, status below. HTML escapes user-controlled strings. World resources are real persistence ports; never cache world between calls or invent returned records.

Pass the resource’s own key as the const key argument to every load/save. Each KEY.load uses its named top-level world key; KEY.save replaces only that key. Native adapters bind these ports to shared persistence.
