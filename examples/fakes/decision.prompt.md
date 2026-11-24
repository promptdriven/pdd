# decision

`decision.mjs` exports module functions decideReply(reply) and doLookup(service, id). decideReply is pure: reply.available true returns `{label:"Available"}`; false returns `{label:"Unavailable"}`. doLookup calls service.lookup once with `{id}` and applies that same decision to the reply. Runtime operations carry reply or id in objects. No live network access occurs here. The service callback is the sole effect boundary.

## Dependencies

None.
