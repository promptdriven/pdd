# Determine an issue author's trust

As a repository maintainer, I can distinguish an outside issue author, so that later skills can apply the trust rule.

## Acceptance criteria

1. An issue by owner Ada is trusted.
2. An issue by write collaborator Bo is trusted.
3. An issue by explicitly trusted Dana is trusted when GitHub provides neither owner nor writers.
4. An issue by outside author Eve is not trusted when GitHub provides neither owner nor writers.

## Rules to check

- A future native skill test must check that, when GitHub supplies neither owner nor writers, only explicitly trusted names qualify for full auto and no other author's issue gets full auto.
