# Exact scenario numbers

Own `src/scenario-json.mjs`. This module is the one owner of how pdd reads and
writes numbers in Runtime scenario files (`prompt-runtime.program-scenario.v1`
test vectors), so that a whole number is never rounded on its way through pdd.

## Why

A scenario file is JSON. JSON writes a whole number as plain digits of any
length, for example `4250129834582680692326400` (3600 × 2^70 seconds). The
JavaScript `JSON.parse` turns every number into a Number. A Number holds whole
numbers exactly only up to ±(2^53 − 1) (`Number.MAX_SAFE_INTEGER`). Above that,
`JSON.parse` silently picks the nearest Number: `9007199254740993` becomes
`9007199254740992`. A test value that changes without a sign makes pdd show,
compare and approve a value that the author did not write.

## The representation

An **exact integer literal** is a JSON number token that matches
`-?(0|[1-9][0-9]*)`: digits with an optional leading minus, and no fraction and
no exponent. Its meaning is the exact whole number of its digits, at any size.
This is the lossless representation of a large whole number in a scenario and in
a Runtime interface schema. There is no wrapper object and no new schema
keyword: `"type": "integer"` means any whole number.

An **exact Number spelling** is the shortest JavaScript spelling of a Number with an
exponent: `String(n)` from 1e21 (for example `4.2501298345826807e+24` for 3600 × 2^70),
`n.toExponential()` below 1e21 (for example `1.152921504606847e+18` for 2^60; `String(n)`
is plain digits there, an integer literal). JavaScript and Python read it as exactly that
Number, so for a parameter that takes a Number it is also lossless. It exists only for
whole numbers that a Number holds exactly.

The PDD interpreter refuses exact integer literals outside ±(2^53 − 1) today
(`scenario-integer-out-of-range`, in `prompt_runtime/program_scenario.py`
`_validate_scenario_integers`), and it admits an exact Number spelling with
`"type": "integer"`. So a test for a Number parameter uses the exact Number
spelling now. A value that no Number holds exactly (for example 2^53 + 1, or any
BigInt parameter) keeps its exact integer literal; only the repository's own
vector test can check it until the interpreter accepts it. A string form changes
the declared type, so use it only when the public contract takes a string.

Every other number token keeps the value that `JSON.parse` gives. A token with
a fraction or an exponent (`1e21`, `2.5`, `9007199254740993.0`) is a
floating-point value. Such a token can lose digits on the way:
`9007199254740993.0` reads as `9007199254740992`. This keeps the meaning of every existing scenario file:
all their whole numbers are within ±(2^53 − 1), and their other numbers are read
as before.

## Exports

`parseScenarioJson(text)` parses one JSON text like `JSON.parse`, with one
difference: an exact integer literal outside ±(2^53 − 1) becomes a BigInt with
the exact value of its digits. An exact integer literal inside that range
stays a Number. `-0` stays negative zero. Invalid JSON throws the same
`SyntaxError` as `JSON.parse`. Read the token text through the reviver context
(`context.source`, Node 22); never rebuild the digits from the Number.

`stringifyScenarioJson(value, space)` is `JSON.stringify(value, null, space)`,
except that it writes each BigInt as plain digits (a JSON raw value). For a
value without a BigInt the output is byte-identical to `JSON.stringify`. So
`stringifyScenarioJson(parseScenarioJson(text))` keeps every exact integer
literal digit for digit. `undefined` at the top level returns `undefined`, as
`JSON.stringify` does.

`exactNumber(value)` gives the Number for a native parameter that takes a
Number. A Number is returned unchanged. A BigInt is returned as a Number only
when that Number has exactly the same value (for example 3600 × 2^70). When no
Number has the exact value (for example `9007199254740993n`), throw a
`RangeError` with `code` `scenario-number-inexact`, whose message names the
exact digits and the nearest Number. Any other type throws a `TypeError` with
the same code. Never round.

`exactValue(value)` gives the canonical form used to compare a native result
with a scenario value. A whole Number outside ±(2^53 − 1) becomes the BigInt
of its exact value. A BigInt inside that range becomes a Number. Arrays and
plain objects are copied with each member converted; other values are
returned unchanged. Two values that `exactValue` maps to deeply equal results
are the same JSON value. Example: the Number 3600 × 2^70 and the literal
`4250129834582680692326400` are the same; the Number 2^53 and the literal
`9007199254740993` are not.

`roundedNumberTokens(text)` lists each number token with a fraction or an
exponent whose digits change when it is read as a Number, as `{path, source,
value}` in document order: `path` is the list of keys and indexes, `source` the
token text and `value` the Number. Compare digits and exponent, not spelling:
`1E5`, `100000.0` and `1e5` name the same value; `9007199254740993.0` (read as
`9007199254740992`) and `1e400` (read as `Infinity`) are listed. Exact integer
literals are never listed. Invalid JSON throws like `JSON.parse`.

`exactIntegerLeaves(value)` lists each BigInt inside a parsed value as
`{pointer, value}` in document order: `pointer` is the RFC 6901 JSON Pointer
(`~` as `~0`, `/` as `~1`) and `value` is the decimal digits string.
`withExactIntegers(value, leaves)` returns a copy of a JSON-safe value with a
BigInt placed at each listed pointer whose current member is a Number that
equals the BigInt's nearest Number. Other pointers are ignored. Together they
let a JSON-only record keep exact digits beside its ordinary copy. `jsonSafe(value)`
returns a copy with each BigInt replaced by its nearest Number, which equals
what `JSON.parse` gives for the same digits.

## Native replay

A repository's own vector test reads its scenario with these rules. In
JavaScript, the whole rule is one reviver:

```js
const scenario = JSON.parse(text, (key, value, context) =>
  typeof value === 'number' && /^-?(?:0|[1-9][0-9]*)$/.test(context.source) && !Number.isSafeInteger(value)
    ? BigInt(context.source) : value);
```

A public function that takes a Number receives `exactNumber(input)`; one that
takes a BigInt receives the BigInt. Compare a result with
`assert.deepStrictEqual(exactValue(actual), exactValue(expected))`. A value that
has no exact Number fails the replay; it is never rounded.

The module does no I/O and keeps no state. It is native-only: its inputs and
results contain BigInt values, which a JSON transport cannot carry, so Runtime
cannot check it; native tests own it.

## Dependencies

None.
