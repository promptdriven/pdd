# Whole-product Simulator

Use one Simulator session to follow a journey through several product parts.
The product map defines the parts. Their app maps define screens and actions.
The product plan can define an ordered background chain after each tap.
Parts without screens can contribute data and background operations.

```sh
pdd simulate --product --journey J1 --max-calls 30
pdd test --journeys J1 --max-calls 30
```

`simulate` starts an interactive session. `test` checks the authored journey
steps and expected results. The allowance covers the whole session or check.
The setup also checks a separate limit of 40 calls for one tap, including
background operations, child calls, caller continuations and drawing.

The service must advertise `product-parts-v1` when the client requests it.
Without that capability, setup stops before uploading source. Product part
names in activity rows come from the admitted source metadata.

## Verify with the coffee example

Copy [the coffee example](../examples/coffee-pickup/README.md) into an empty
Git repository. Follow its root-path instructions. Copy the linked J1 Story
and scenario into that repository. Use the commands above.

Open the phone menu, choose a latte, then mark its ticket done on the barista
screen. The phone shows Ready. Inspect the activity rows for phone, server
and barista labels. Refresh the page and check that the data and labels remain.
Reopen the same Story with `pdd simulate STORY`; it retains the product session.
Use `--new` only to deliberately start a separate session.

Generated app maps and world seeds exist only in the uploaded snapshot.
Authored maps and scenario steps remain unchanged. Shared starting data is
optional. Part seeds override shared starting data; explicit journey values
apply last. Conflicting writers stop setup before upload.

## Supported composition

Local screen names take priority within their part. Cross-part destinations
use qualified names such as `barista/board`. Parts retain separate screen
state. Compatible routers and stylesheets are shared.

Setup refuses ambiguous ownership, incompatible routers, unsupported map
extension fields, unsafe sources and unknown call bounds. The explanation
names the authored source. Keep an unsupported map in a standalone session
until its composition behavior is specified.
