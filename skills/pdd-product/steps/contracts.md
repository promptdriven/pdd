# contracts

For medium and large products, write `contracts/*.md` with one owner and a JSON
schema under each `### record` heading. Follow [the contract format](../references/files.md#contracts)
for world ownership and the shared seed. Prefer explicit optional Schema links
for new plans; existing Key or Path tables may omit them. Use explicit
`$contract` shape references between parts. Check normal, refusal and empty-world examples.
Run `pdd contracts --check`; report its actual result and every problem or
unavailable validation. This step makes no PDD interpreter lint, test or simulation call.
Leave unresolved choices visible for the person. For small products, skip this.
