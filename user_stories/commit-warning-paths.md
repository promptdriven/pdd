# See the files committed at publication

As a person reviewing a workflow PR, I can see the exact paths of files pdd automatically committed in its warning.

## Acceptance criteria

1. When the first unstaged file is `value.mjs`, the automatic commit warning names `value.mjs`, including its first character.
2. When `value.mjs` and `z-new.txt` are committed together, the warning names both exact paths.
3. When the only untracked file is `new.txt`, the warning names `new.txt`.
4. When files named `space name.txt` and `quote"name.txt` are committed, the warning names those exact paths without Git's added quoting or escaping.
5. When `value.mjs` is renamed to `renamed file.mjs`, the warning names `renamed file.mjs` as the committed path, not the source or a `source -> destination` representation.
6. With no uncommitted files, pdd adds no automatic commit warning. Existing workflow gates, commit-all behavior and warning wording otherwise stay the same.

## Rules to check

The warning must not drop or add characters to a committed destination path, even when Git's status output begins with a space or quotes a path.
