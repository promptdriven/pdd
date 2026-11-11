# Respect a zero upper bound in clamp

The clamp helper accepts zero as an upper bound, but `clamp(7, -10, 0)` returns
7. It must return 0. Add this missing native regression before fixing the code;
it must fail on the base for this wrong result. Also check that
`clamp(-3, -10, 0)` stays -3. Preserve the default 0 through 100 range and the
existing tests. The owning prompt already requires a valid zero upper bound;
do not change that expected contract. Run `npm test`.
