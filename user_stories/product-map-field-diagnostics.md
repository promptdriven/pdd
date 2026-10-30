# Find the missing screen setting

I can see which required screen setting I need to supply before trying my product.

## Acceptance criteria

1. When a screen is missing prompt_path, Try names prompt_path in its error.
2. When a screen is missing operation, Try names operation in its error.
3. When a screen is missing source, Try names source in its error.
4. When a screen is missing format, Try names format in its error.
5. When a screen is missing input, Try names input in its error.
6. When a screen is missing result_pointer, Try names result_pointer in its error.

## Verification scope

Runtime error checks support only the error code, so they cannot check these field names. The ordinary Node tests replay all six missing-field cases from `test/native/product-map-field-diagnostics.json`, checking both the refusal code and the named field. This Story has no Runtime pass claim.
