# I use a shared record in my schemas

## Acceptance criteria

1. A record heading with spaces and its heading fragment expand to the same schema.
2. A JSON Pointer can select escaped names and array index 0, including nested shared records.
3. A missing record is refused instead of producing a partial schema.
4. A cycle of shared records is refused.
5. An ambiguous heading is refused instead of choosing a record.
6. Literal defaults retain their values during expansion; source with no applicable reference keeps its exact bytes.
7. A local title and description survive expansion of a shared schema.
8. A local constraint beside a shared reference is refused instead of silently overriding it.

## Rules to check

References apply to schema positions only. Check and Try must validate and upload the same expanded bytes. Missing references stop before upload; real schema $ref remains refused. JSON numbers such as 9007199254740993 retain their exact number text in source and provenance; __proto__ and constructor remain ordinary own keys. Native capture tests must also cover no-reference tar identity, selected-only privacy, snapshot retries, size limits and synchronous readPrompt compatibility.

Runtime check: expansion entry bound with supplied file stat/read replies; native upload, privacy and CLI effects need native verification.
