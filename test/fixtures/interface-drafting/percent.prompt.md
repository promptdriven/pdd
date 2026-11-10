# percent

This module displays a basis-point rate as a percentage beside a price. It owns the percentage format of the library. This is new behavior authorized by issue #20; existing price, duration and word contracts remain unchanged.

Public binding: module function `formatPercent(basisPoints)` in `src/percent.js`, exported from `tiny-format/percent`. It takes a Number of basis points and returns a string. In the Runtime interface, operation `formatPercent` takes an object with required numeric `basisPoints` and returns an object with required string `text`, the returned string; neither object has additional properties.

## Percentage format

100 basis points equal one percent. Accept a Number only if it is a safe integer. Show the exact rate with two decimal digits and a trailing `%`, without spaces or grouping separators. Use the magnitude for the digits and a leading minus sign for negative rates. Zero, including negative zero, is `0.00%`. Rates above 100 percent are allowed; do not clamp or round.

For example, 1 is `0.01%`, 1250 is `12.50%`, 10000 is `100.00%`, and -125 is `-1.25%`.

## Refused rates

Fractions, non-number values, NaN, infinities and unsafe integers are refused. Throw a `RangeError` with `code` equal to `invalid-basis-points`. No input is rounded.

There are no external resources, operating-system commands or saved data.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{
  "entries": [
    {
      "operation": "formatPercent",
      "input_schema": {
        "type": "object",
        "properties": {
          "basisPoints": {
            "type": "number"
          }
        },
        "required": [
          "basisPoints"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "text": {
            "type": "string"
          }
        },
        "required": [
          "text"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid-basis-points"
      ]
    }
  ],
  "calls": [],
  "resources": [],
  "limits": {
    "max_steps": 4,
    "max_model_calls": 2
  },
  "conventions": [],
  "status": "approved",
  "prose_sha256": "70383036fc22f8729960ebde0f07cd1aaefa8b97b6f1c8a4f6e3759d589d8e85"
}
```
</details>
