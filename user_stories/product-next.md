# Find the next product runs

I can choose a ready run and see what the other runs wait for.

## Acceptance criteria

1. The checked-out coffee plan offers server-1, phone-1 and barista-1 in plan order, and says they can run in parallel or one person can start them in order.
2. The journeys run waits for server-1, phone-1 and barista-1.

## Rules to check

Only this run's own merged implementation makes its dependents ready. An unrelated
PR, fork or comment must not unlock them. A cycle, including a self-dependency,
shows its path while unrelated ready runs remain available. It does not become a
hard gate when I explicitly start a run.
