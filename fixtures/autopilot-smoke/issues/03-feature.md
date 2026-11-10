# Allow sum to start from an optional value

Let callers supply an optional second finite numeric argument to sum, used as
the starting total. `sum([1, 2], 10)` must return 13, and `sum([], 10)` must
return 10. Omitting the argument keeps the existing behavior, including
`sum([])` returning 0. Update the owning prompt first, add native tests for these
examples, implement the feature, and document the optional argument. Preserve
clamp and slugify behavior. Run `npm test`. No dependencies are needed.
