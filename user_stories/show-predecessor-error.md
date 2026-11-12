# Show a reported predecessor error

As a person reading a refused Check, I want its verified earlier error and input reference, so that I can investigate with the report facts.

## Acceptance criteria

1. When a completed Check refusal has a verified earlier error, I see the dependent step, input pointer, predecessor step, result pointer and reported error code in terminal output and JSON.
2. When dependency evidence is missing or ambiguous, I see the existing refusal without an added dependency diagnosis.
3. The original refusal, check results, counts, usage and recovery advice stay the same; showing or reading the diagnosis never resends the Check.

## Rules to check

- Use only completed Check report facts and the original captured authored steps. An exact `samples[N].steps[M]` section anchors the sample and captured authored dependent index. Its reported dependent row may be absent; an existing conflicting identity is rejected. A relative `at` location may corroborate M only with that sample anchor. Other supplied locations must agree. A bare step index supplies no sample. Never borrow evidence from another sample.
- A dependency is an exact authored `$step_result` object in the dependent input, with string predecessor identity and result pointer. Extra keys, reference-like strings, malformed objects and guessed message links supply no fact.
- The predecessor must be uniquely identified in authored steps, earlier than the dependent step, and uniquely reported in the same sample. Require a nonblank string error code and no normal result. Null or absent result means no normal result; any non-null value, including false or zero, suppresses the diagnosis.
- Missing, conflicting, duplicate or redacted identities or error codes cannot establish a dependency. Missing authored references cannot be replaced by current source.
- Show each distinct input reference in authored traversal order. Different input pointers remain distinct. Escape `/` and `~` in input pointer tokens with JSON Pointer rules.
- Publish only the five dependency strings described by the owning prompt. Clean controls, known secrets, recognized credential tokens and server host paths. Preserve reference-pointer structure while removing embedded secrets and controls. Do not expose application payloads, traces, worlds or resource data.
- Dependency facts cannot alter the refusal code, failed-check identity or values, verdict, summary counts, usage, model, exit precedence, effects, recovery or dispatch. Never infer that a step was unexecuted or that a new request is safe from an error code.
- A completed saved read with its original report and captured authored input shows the same diagnosis without another Check POST. A UUID-only or older read without those references keeps the refusal without a guessed dependency.

## Concrete example

For a synthetic report, "unknown-order" reports "board-unavailable" and has a null result. The captured input of "draw-refusal" references that step's "/loaded" result at input "/loaded". Its refusal keeps "key-error" and adds:

```text
  Dependency: step "draw-refusal" input "/loaded" references step "unknown-order" result "/loaded"; that step reported error code "board-unavailable".
```

JSON adds `dependency_errors` to that refusal, with `step_id`, `input_path`, `predecessor_step_id`, `result_path` and `error_code`. With no supported fact, omit that field.

## Verification boundary

The prompt's partial Runtime entry accepts already projected JSON rows. Its small scenario checks dependency retention/absence and refusal metadata. Native tests separately check raw report association, terminal output, unchanged checks/counts/accounting/recovery and completed saved reads with no additional Check POST. A partial prompt check alone does not prove those effects.

## What must not change

Keep existing failed-check identities, original report/request, counts, partial effects, known/unknown usage, summary and exit policy, report/model metadata and recovery advice. This CLI diagnosis does not repair Runtime execution or the original application error. The original private scenario is not reproduced by these synthetic tests. Issue 2734 stays open.
