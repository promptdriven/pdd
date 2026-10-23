# Ticket status label

## Purpose

Convert the ticket's status value into a short label for display.

## Public interface

The JavaScript module exports `statusLabel(status)`, which returns a string.

## Behavior

- The exact string `open` returns `Open`.
- The exact string `blocked` returns `Blocked`.
- The exact string `done` returns `Done`.
- Any other string or `null` returns `Unknown`.
- Any value that is neither a string nor `null` throws `TypeError`.

Matching is case-sensitive. The function does not trim, translate, or otherwise rewrite input strings.

## Dependencies

None.
