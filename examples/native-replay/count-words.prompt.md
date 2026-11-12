# Synthetic countWords target

`countWords(text)` returns the number of whitespace-separated words in a string,
with an empty or whitespace-only string producing zero. For a non-string it
throws `TypeError` with message `text must be a string`. This synthetic native
fixture demonstrates a public error outside a string-only Runtime input domain.
It does not define or change a Runtime entry; its missing Runtime interface is
an explicit gap in this synthetic fixture, not a native-only effect claim.

## Dependencies

None.
