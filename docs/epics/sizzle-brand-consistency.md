# Epic: Brand consistency with Sizzle

Align the PromptDriven.ai web UI (`pdd/frontend`) with the branding choices made on
the Sizzle site (`https://video.promptdriven.ai/sizzle`), which are cleaner and more
consistent. Sizzle is a PromptDriven.ai product, so the two surfaces should share one
visual identity.

## Target (Sizzle) branding

- **Logo:** `PromptDriven_Logo_MonoWhite.svg` — a clean **white-filled** "P" speech-bubble
  with **no glow** filter.
- **Brand color system:** `brand-cyan #00d8ff`, `brand-navy #0a0a23`,
  `brand-graphite #1a1b26`, `brand-magenta #ff2aa6`, `brand-purple #8c47ff`,
  `brand-green #18c07a`, `brand-sleet #f5f7fa`, `brand-mute #5b6378`.
- **Fonts:** Inter (sans) + JetBrains Mono (mono) — already used by the main site.
- **Wordmark:** `PromptDriven.ai` lockup next to the logo, cyan accent.

## Current state (`pdd/frontend`) being replaced

- `public/logo.svg`: a glowing **cyan #00e3ff** "P" with a Gaussian-blur glow filter.
- `components/Header.tsx`: text-only heading "Prompt Driven Development IDE" with a generic
  blue (`#3b82f6`) accent, no logo lockup.
- `index.html` `<title>`: "Prompt Driven Development"; Tailwind config has no shared brand
  palette.

## Sub-PRs

This epic is delivered as focused sub-PRs that each target this epic branch
(`epic/sizzle-brand-consistency`):

- [ ] **Logo** — replace `public/logo.svg` with the clean mono-white brand logo.
- [ ] **Colors** — add Sizzle's brand color tokens to the Tailwind config.
- [ ] **Header** — adopt the `PromptDriven.ai` logo + wordmark lockup and cyan accent;
  align the page `<title>`.

Once all sub-PRs merge into this branch, this epic PR merges into `main`.
