# Filter pull requests with no pdd result

As a reviewer triaging pull requests on GitHub, I want runs with no saved `pdd test` or `pdd lint` result to carry the `pdd:no-verdict` label while valid native-only runs stay unlabeled, so that I can filter unverified pull requests without false alarms.

## Acceptance criteria

1. Publishing a pull request with no saved `pdd test` or `pdd lint` result and no valid native-only prompt scope adds the `pdd:no-verdict` GitHub label, creating the repository label when missing while leaving existing labels unchanged.
2. Publishing or refreshing a pull request with a saved `pdd test` or `pdd lint` result, including a failed result, removes `pdd:no-verdict` and preserves other labels.
3. Publishing or refreshing a pull request whose changed owning prompts all validate with `native-only` kind and a nonblank reason records `not-applicable (native-only)` in the pull request description instead of `pdd:no-verdict` and removes `pdd:no-verdict` when present.
4. When a GitHub label request fails during publication, the pull request stays open and prints a retry warning.
