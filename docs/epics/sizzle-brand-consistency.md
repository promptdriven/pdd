# Epic: Brand consistency with Sizzle

Align the PromptDriven.ai web UI (`pdd/frontend`) with the branding choices made on
the Sizzle site (`https://video.promptdriven.ai/sizzle`), which are cleaner and more
consistent. Sizzle is a PromptDriven.ai product, so the two surfaces should share one
visual identity.

**Scope note:** the existing (glowing cyan) logo is **kept**. This epic matches Sizzle's
**text** style and clean look only.

## Target (Sizzle) branding

- **Wordmark text style:** a semibold sans wordmark in near-white `brand-sleet` beside a
  tiny, wide-tracked, uppercase **mono `brand-cyan`** descriptor, baseline-aligned —
  mirroring Sizzle's `Sizzle` / `by Prompt Driven` lockup:
  ```html
  <span class="font-sans font-semibold tracking-[0.01em] text-brand-sleet text-lg">Sizzle</span>
  <span class="font-mono font-medium tracking-[0.12em] text-brand-cyan text-xs">by Prompt Driven</span>
  ```
- **Brand color system:** `brand-cyan #00d8ff`, `brand-navy #0a0a23`,
  `brand-graphite #1a1b26`, `brand-magenta #ff2aa6`, `brand-purple #8c47ff`,
  `brand-green #18c07a`, `brand-sleet #f5f7fa`, `brand-mute #5b6378`.
- **Fonts:** Inter (sans) + JetBrains Mono (mono) — already used by the main site.

## Current state (`pdd/frontend`) being replaced

- `components/Header.tsx`: bold-white heading "Prompt Driven Development IDE" + slogan link
  with a generic blue (`#3b82f6`) accent — busier than Sizzle's lockup.
- `index.html` `<title>`: "Prompt Driven Development"; Tailwind config has no shared brand
  palette.
- `public/logo.svg`: the glowing cyan logo — **kept as-is**.

## Sub-PRs

This epic is delivered as focused sub-PRs that each target this epic branch
(`epic/sizzle-brand-consistency`):

- [ ] **Colors** — add Sizzle's brand color tokens to the Tailwind config.
- [ ] **Header** — match Sizzle's clean wordmark text style (`brand-sleet` semibold sans +
  mono `brand-cyan` descriptor), align the page `<title>`; keep the existing logo.

Once all sub-PRs merge into this branch, this epic PR merges into `main`.
