# service

`service.mjs` exports module function `lookup(service, id)`. Invoke the injected service.lookup callback exactly once with `{id}` and return its `{label}` unchanged. The callback owns network access; the module never calls a network API. Runtime resource service represents this callback. Its fixed test reply is independent of id; exact recorded arguments prove forwarding, not a live service response.

## Dependencies

None.
