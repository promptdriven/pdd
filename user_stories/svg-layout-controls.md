# Check only declared screen controls against the drawing

As a screen author, I want local SVG layout lint to check only declared screen controls against my linked .ui.svg drawing, so that HTML classes, ARIA attributes, container ids and quoted help text are not reported as missing controls while real control mismatches stay visible.

## Acceptance criteria

1. Running `pdd lint --local` on a screen prompt with `<div id="app-shell" class="app"><main id="wait-card" class="body pushed no-dock"><p id="status-chip" class="chip st-waiting" role="status" aria-busy="true">Waiting for approval</p><button id="refresh" name="refresh">Refresh</button><button id="sign-out" name="sign-out-action">Sign out</button></main></div>` against a `.ui.svg` drawing that contains `wait-card`, `status-chip` and `Refresh` (`id="refresh"`) warns for `"Sign out"`, `"sign-out"` and `"sign-out-action"`, emits 0 missing-control warnings for `"app-shell"`, `"app"`, `"body pushed no-dock"`, `"chip st-waiting"`, `"status"` or `"true"`, and exits with code 0.
2. Running `pdd lint --local` on a screen prompt with single-quoted `<div id='shell-frame' class='app-frame compact' role='region' aria-live='polite' aria-busy='false'><button id='retry' name='retry' type='button' class='btn primary' aria-label='Retry connection'>Retry</button></div>` and negated prose `No button shows "Loading..." while idle.` against a `.ui.svg` drawing that contains `Retry` (`id="retry"`) emits 0 warnings and exits with code 0.
3. Running `pdd lint --local` on a screen prompt with ``Use buttons with label "Start". `instructions` says "Arrow keys to steer. Enter to start. P to pause. R to restart." Also explain "Automatic moves wait at least 1 second plus interpreter time." No button directly advances a move: the host timer does that automatically while the live Screen is visible.`` against a `.ui.svg` drawing showing `Start` and both help texts emits 0 warnings, including 0 warnings for `" Also explain "`, and exits with code 0.
4. Running `pdd lint --local` on a 2048-like screen prompt with four direction buttons in prose and `SCORE`, `SEED` (`#score`, `#seed`) and `READY` (`#status`) in the `.ui.svg` drawing still warns for `"move-down"`, `"move-left"`, `"move-right"`, `"move-up"`, `label "READY"`, `region #score`, `region #seed` and `region #status`, and exits with code 0.

## What must not change

- SVG layout warnings in `pdd lint --local` and `pdd lint` remain advisory (`Warning: SVG layout <prompt> -> <drawing>: ...`), use 0 AI calls locally, and never refuse a test or approve a prompt.
- Affirmative prose and HTML control declarations (`id`, `name`, button `value`, native `<button>` text label, quoted control label such as `Button "Go & win" with id="go"`, backticked control ids, and directional-control phrases) still warn when absent from visible drawing parts.
- Reverse drawing checks for visible nonnumeric `<text>` labels absent from prompt prose and visible `.ui.svg` region `id`s unacknowledged in prose or `## Appearance` stay unchanged.
- Comment and CDATA rules, XML entity decoding, hidden and `context-only` exclusions, SVG safety checks, and `pdd-workspace.json` path filtering stay unchanged.

## Rules to check

- Non-control HTML attributes (`class`, `role`, `aria-*`, `data-*`, `style`, `type`, `placeholder`, `title`, `href`, whether double- or single-quoted) and `id` attributes on non-control HTML elements (`div`, `main`, `section`, `p`, `span`, headings, lists, `form`, `input type="hidden"`) never become prompt controls. Forbidden: any `control "<value>": prompt control absent from drawing` warning whose `<value>` originates only from a non-control attribute or non-control container `id`.
- Prose sentence and clause splitting tracks quote and Markdown code-span boundaries so sentence punctuation inside quoted copy never splits a literal or pairs adjacent quotes across literals. Forbidden: any `control "<value>": prompt control absent from drawing` warning whose `<value>` is connecting prose outside quotes (such as `" Also explain "`) or non-control instruction/status copy.
- Negated control clauses (`no button`, `no controls`, `without a button`, `without controls`) declare no required drawing controls. Forbidden: a `prompt control absent from drawing` warning extracted from a negated control clause.
- Every affirmative control `id`, `name`, button `value`, native `<button>` visible label, prose quoted control label, prose backticked control id and directional-control target absent from visible `.ui.svg` parts (`id` or `<text>`) is reported. Forbidden: suppressing a genuine missing control warning when non-control HTML attributes or multi-sentence help strings appear in the same prompt.
