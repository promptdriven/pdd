# factory

`factory.mjs` exports module function `createGreeter(prefix)`, returning an object with method `greet(name)`. Each greeter captures its own `prefix`; `greet` returns `{ text: prefix + name }` without changing it. Runtime `createGreeter({ prefix })` is a `Greeter` factory: store `{ handle, config: { prefix } }` via `instances.store` using the executor-issued opaque `handle`, and return `{ handle }`. Runtime `greet({ handle, name })` loads `{ config: { prefix } }` once via `instances.load({ handle })` and returns `{ text }`. Handles are opaque; never invent them. The `instances` collection represents closure state, not a new public argument to the native method.

## Dependencies

None.
