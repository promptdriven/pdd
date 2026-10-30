# Track product progress

I can see which planned Stories passed on current files and which need another check.

## Acceptance criteria

1. With P01 current and P02 passed only on older files, phone shows one pass, one stale and two not run out of four Stories.
2. The unrelated P010 result is not counted as P01, and the server and barista each have four not-run Stories.
3. Slice 1 includes the twelve part Stories and J1 once, with one pass, one stale and eleven not run.

## Rules to check

Only a pass bound to current files is a local current pass. P010 must never satisfy P01. A stale pass must not appear as current.
