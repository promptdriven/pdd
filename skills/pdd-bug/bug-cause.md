# Cause and relation rules

Relations use `issue` (another open issue), `kind`, `source` (`issue:N` or `code:PATH`), `quote` (exact evidence) and `link`. Allowed links: needs → blocked by; duplicate → duplicate; same cause → none or blocked by; same class → none or sub-issue under existing `Class: <short name>`; related → none. pdd validates every exact quote before link writes. Evidence does not prove diagnosis; shared cause alone implies no dependency.
