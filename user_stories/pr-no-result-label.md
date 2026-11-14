# Filter pull requests with no pdd result

As a reviewer triaging pull requests on GitHub, I want runs with no usable saved `pdd test` or `pdd lint` verdict to carry the `pdd:no-verdict` label while valid native-only runs stay unlabeled, so that I can filter unverified pull requests without false alarms.

## Acceptance criteria

1. Publishing or refreshing a pull request with no usable saved `pdd test` or `pdd lint` verdict and no valid native-only prompt scope adds the `pdd:no-verdict` GitHub label after the pull request body is written, creating the repository label when missing while leaving existing labels unchanged.
2. Publishing or refreshing a pull request with a usable saved `pdd test` or `pdd lint` verdict, including a failed or refused result, removes `pdd:no-verdict` and preserves other labels, whereas a local-only or partial unfinished batch still counts as no verdict.
3. Publishing or refreshing a pull request whose committed run changes resolve only to prompts with `native-only` kind and a nonblank reason records `not-applicable (native-only)` for `pdd test` instead of `pdd:no-verdict` and removes `pdd:no-verdict` when present, even when `pdd lint` was also saved.
4. When a GitHub label request fails during publication or refresh, the pull request stays open and prints a retry warning.
