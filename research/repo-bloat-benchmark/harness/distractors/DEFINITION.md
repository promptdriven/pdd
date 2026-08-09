# What is a "distractor file"?

Machine-checkable restatement of design.md **§5.0**. The generator
(`generator.py`) enforces this contract for **every** admitted file, whatever
its source mode; `definition.py` is the single implementation of the checks,
and the test suite exercises each condition.

## Definition

A file `D` is a **distractor** for a scenario `(core, task, visible_tests,
hidden_verifier)` iff **all** of the following hold:

| # | Condition | Machine check (`definition.py`) |
|---|-----------|--------------------------------|
| 1 | **Structural irrelevance** — `D ∉ closure(core)`: no core file imports/includes/loads `D`, and `D` is not a target file | destination path not in `core_files`; module name not importable by any core import statement (static import scan); not in `target_files` |
| 2 | **Behavior neutrality** — materializing/removing `D` changes no visible-test or hidden-verifier outcome | forbidden ambient-side-effect basenames rejected (`conftest.py`, `sitecustomize.py`, pytest plugins, packaging/config entrypoints); destination must not shadow a core module (same importable name); dynamic-import red-flag scan. Final authority: the §4.1.2 oracle equivalence gate re-runs both suites per materialized variant |
| 3 | **Plausibility** — project language and idiom; would not read as filler | parses (`ast`) for Python; identifier-vocabulary overlap with the core ≥ recorded floor; verbatim project files pass by construction |
| 4 | **No leakage** — no hidden-verifier or oracle-patch content | content screened against the scenario's hidden-assertion denylist |
| 5 | **No tell** — nothing marks `D` as a distractor | destination path/name/content screened for marker strings (`distractor`, `filler`, `synthetic`, `decoy`, …) |

Checks 1, 2, 4, 5 are hard gates (violation ⇒ file rejected, generation
aborts if requested size cannot be met legally). Check 3 is a hard gate for
generated files and a recorded no-op for verbatim (`regrow`) files.

## Source modes (design §5.0.1)

One definition, three deterministic sources, fixed cascade
(`regrow` → `mutate` → `template`), each file's `mode` recorded in the
manifest so per-mode read/penetration rates can be reported:

- **`regrow`** — verbatim out-of-core project files at their original paths.
- **`mutate`** — seeded, semantics-preserving derivations of pool files
  (identifier/docstring renames from a recorded vocabulary map), placed at
  plausible non-colliding sibling paths. Extends the pool past its natural
  size.
- **`template`** — synthetic modules from parameterized skeletons filled with
  vocabulary harvested from the core; size-tunable, used as the terminal
  filler so any token budget converges (50x and breakdown-probe steps).

## Why a definition at all

The review feedback asked for distractors to be *defined*, then *generated
from the definition* and *scaled aggressively*. Making the definition a
checkable contract (rather than prose) is what lets three different sources
share one guarantee — and lets the 50x/probe conditions exist without
weakening the experiment's "only one thing varies" principle.
