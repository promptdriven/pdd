# Share source through links inside my repository

I can keep shared source in one folder and link to it from the folders that use it, then run `pdd test` without rearranging my repository.

## Acceptance criteria

1. A selected direct file link or a selected file inside a linked folder sends the final Git-visible regular file's exact bytes under the authored path, as a regular archive entry with mode 0600.
2. `pdd test --files` shows each linked file as `authored/path -> canonical/target` with its byte size, offline.
3. Outside targets, broken links, loops, secret link names, secret target names and targets that are not Git-visible are refused before upload; the message names the link and its target and explains why.
4. Source metadata, except the strict no-link bindings inventory, and raw preparation/reference reads use the same safe link policy; reference-only source stays unselected and relative Markdown dependencies keep the authored linked path as their base.
5. Link resolution and bytes belong to one consistent snapshot; source SHA, archive ordering/PAX, limits, other privacy/type/submodule refusals, prepared output destinations and executable/write-target refusals retain their existing guarantees.

## Rules to check

Only an entirely in-repository resolution to a Git-visible regular target may supply linked bytes. A changed chain, ancestor or final file retries the whole capture; sending outside, secret or unobserved replacement bytes is forbidden. A link does not waive upload byte/file limits. Safe source reads do not authorize writing through links, executing linked bindings or reading a linked bindings inventory (including linked ancestors of declared paths). Secret-looking generated paths refuse even below missing folders, and unsafe missing paths refuse on stat. Linked Story title fallback uses the checked target size and identity. Refusals identify the link whose destination fails; an ignored authored link is described as the link itself not being Git-visible. Ordinary non-link refusal wording stays unchanged. Forty traversed links are allowed; longer chains and expanding loops terminate with a refusal.

Runtime check: NOT REPLAYED. Native OS/Git identity, races and tar headers have no executable Runtime port in these owning prompts. The native case inventory and ordinary Node tests record concrete coverage; they are not interpreter scenarios or an approval.
