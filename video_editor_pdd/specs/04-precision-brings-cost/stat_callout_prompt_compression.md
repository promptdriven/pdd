[Remotion] Statistic Callout — Prompt Compression Through Tests

## Overlay Spec
- Type: animated statistic callout
- Trigger: synced to narration "the more walls you have, the less you need to specify"
- Duration: 5s (fade-in 0.5s, hold 4s, fade-out 0.5s)
- Position: center

## Content
- Primary stat: "50 → 10 lines"
- Label: "prompt size as tests accumulate"
- Secondary stat: "47 tests"
- Secondary label: "absorb edge-case precision"
- Source: "PDD precision tradeoff"

## Styling
- Primary stat: Inter Black, 72px, gold (#F59E0B)
- Arrow between numbers: animated shrink transition
- Label: Inter Regular, 24px, white 80% opacity
- Secondary stat: Inter Black, 48px, green (#22C55E)
- Secondary label: Inter Regular, 20px, green (#22C55E) 60% opacity
- Source: Inter Light, 16px, white 60% opacity
- Background: rounded rect, #1E293B, 80% opacity, blur backdrop
- Border: 1px solid #334155
- Animation: "50" counter animates down to "10" while test count animates up to "47"
