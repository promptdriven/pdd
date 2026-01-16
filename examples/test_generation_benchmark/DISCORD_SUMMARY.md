# Test Generation Benchmark: Code-based vs TDD

We benchmarked two ways to generate tests with `pdd test`:

**Code-based (original):** `pdd test prompt.prompt src/module.py`
- Analyzes actual implementation code

**TDD/Example-based (new):** `pdd test prompt.prompt examples/module_example.py`
- Analyzes usage examples showing intended behavior
- Triggered by `_example` suffix in filename

## Results

| Metric | Code-based | Example-based |
|--------|-----------|---------------|
| Test functions | 20 | 37 |
| Tests passed | 17 | 34 |
| Private method refs | 0 | 0 |

## Key Findings

1. **Example-based generated 85% more tests** - more granular, better failure isolation

2. **Neither referenced private methods** - both respected "don't test internals" guidance

3. **Example-based tests are more portable** - one assertion per function vs batched loops

## When to Use Each

| Use Example-based (TDD) | Use Code-based |
|------------------------|----------------|
| Writing tests first | Testing existing code |
| API contract matters | Need coverage analysis |
| Implementation will change | Verifying specific behaviors |

## TL;DR

For new PDD development, prefer TDD approach - generates more comprehensive tests focused on intent, not implementation accidents.

---

Try it yourself:
```bash
cd examples/test_generation_benchmark
make benchmark
```

**Feedback welcome!** Does this match your experience? Any edge cases we should test?
