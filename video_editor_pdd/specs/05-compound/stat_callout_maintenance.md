[Remotion] Statistic Callout — Maintenance Cost Dominance

## Overlay Spec
- Type: animated statistic callout
- Trigger: synced to narration "Eighty to ninety percent of software cost isn't building the initial system"
- Duration: 6s (fade-in 0.5s, hold 5s, fade-out 0.5s)
- Position: center

## Content
- Primary stat: "80–90%"
- Label: "of software cost is maintenance"
- Secondary stats:
  - "+40%" / "maintenance spend with high tech debt" / "McKinsey"
  - "33%" / "of dev time lost to debt" / "Stripe"
- Source: "McKinsey, Stripe developer surveys"

## Styling
- Primary stat: Inter Black, 84px, red (#EF4444)
- Counter animation: rolls up from 0% to 90%
- Label: Inter Regular, 24px, white 80% opacity
- Secondary stats: Inter Bold, 40px, amber (#F59E0B)
- Secondary labels: Inter Regular, 18px, white 60% opacity
- Sources: Inter Light, 14px, white 50% opacity
- Background: rounded rect, #1E293B, 80% opacity, blur backdrop
- Border: 1px solid #334155
- Animation: primary stat appears first, secondary stats cascade in with 0.4s stagger
