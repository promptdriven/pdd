# Optional client hooks for public command owners

`src/client-hooks.mjs` owns module function
`getOptionalClientHooks({clientAdapter,phoneCli,updateModule} = {})`. It exposes
the optional bindings used by status, doctor and update owners without loading
their implementations. Preserve the existing fleet binding names, argument
shapes, receiver and returned values. This module selects functions; it grants
no authority and performs no command, diagnostic, release check or installation.

Return a frozen object containing only available function bindings from this
table. A missing adapter/module or a nonfunction member omits that key. Preserve
the `phoneCli` alias only when `clientAdapter` is undefined; explicit null disables
the client hooks. The update module remains an independent registration and never
falls back to a similarly named member of the client adapter.

| Result key | Source | Existing invocation contract |
| --- | --- | --- |
| runStatusCommand | selected client adapter | `(argv, ports)`; argv excludes status; returns integer exit code 0–255 |
| doctorChecks | selected client adapter | `({mode})`; mode text/json/report/check-only/cleanup; returns `{checks,report?}` |
| runUpdateCommand | updateModule | `({action,value,fleet,force}, ports)`; returns `{state,code,message}` with code 0/1/2 |

For doctor, checks have `{id,state,detail,next}` with state pass/fail/skip; the
optional report supplies versions, installPhases, accountStates, expiries,
lastGoodAt, diskFreeBytes or logLines. For update, the registered module owns
release selection and its effects; this helper never selects a release itself.

Resolution never invokes a selected method, mutates supplied objects, prints,
reads files, imports an add-on or accesses a service. Bind each method to its
original adapter/module so receiver-based implementations keep working. Forward
the caller's arguments and return value without wrapping, cloning or retrying;
preserve Promise identity and thrown/rejected failures. Throwing property access
likewise remains the composing caller's failure, not proof that the capability
is absent. Public owners retain validation, redaction, absent-client messaging
and failure handling; absence must not be represented as successful diagnostics
or proof of no available update.

No new status, doctor or update CLI route is introduced. A public owner imports
this helper and feature-detects the returned key before deciding its own fallback.

## Dependencies

- [CLI adapter registration](pdd-cli.prompt.md#optional-client-registration):
  required authoring/generation context for explicit clientAdapter registration
  and its legacy phoneCli alias. No runtime import of that owner is required.
- JavaScript function binding and Object.freeze: runtime facilities; no package,
  filesystem or service dependency.
