[Remotion] Statistic Callout — CISQ Technical Debt

## Overlay Spec
- Type: animated statistic callout
- Trigger: synced to narration "CISQ puts the US total at one-point-five-two trillion dollars annually"
- Duration: 5s (fade-in 0.5s, hold 4s, fade-out 0.5s)
- Position: center-right

## Content
- Primary stat: "$1.52T"
- Label: "annual US technical debt"
- Secondary stat: "Debt × (1 + Rate)^Time"
- Secondary label: "compound interest curve"
- Source: "CISQ — The Cost of Poor Software Quality"

## Styling
- Primary stat: Inter Black, 72px, gold (#F59E0B)
- Counter animation: rolls up from $0 to $1.52T
- Label: Inter Regular, 24px, white 80% opacity
- Secondary stat: Inter Bold, 36px, red (#EF4444)
- Secondary label: Inter Regular, 20px, red (#EF4444) 60% opacity
- Source: Inter Light, 16px, white 60% opacity
- Background: rounded rect, #1E293B, 80% opacity, blur backdrop
- Border: 1px solid #334155
