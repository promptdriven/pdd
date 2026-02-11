# AUDIT: S02 V10 -- ChipDesign:netlists

## Scene Info
- **Component**: ChipDesign:netlists (non-deterministic synthesis)
- **Time Range**: 95.2s - 108.5s
- **Frames Reviewed**: t=97s, t=102s, t=107s

## Script Visual
> "Same Verilog code runs through synthesis three times. Three visibly different gate-level netlists appear side by side. All different. Then a green checkmark appears over each: 'Functionally equivalent'."

## Observed Visual
Frame at t=97s: The same Verilog ALU code is shown at top center. Label "SAME VERILOG SOURCE" below it. The code feeds into synthesis -- but at this point the three netlists are not yet all visible. The layout is preparing for the three-column comparison.

Frame at t=102s: Full three-column layout now visible. Same Verilog code at top, "SAME VERILOG SOURCE" label. Three arrows lead down to three separate "SYNTHESIS" boxes. Below each, a different gate-level netlist diagram:
- Run 1: gate symbols (&, >=1, 1) in one arrangement
- Run 2: different gate arrangement (1, >=1 symbols)
Each labeled "Run 1", "Run 2". The layouts are visibly different.

Frame at t=107s: All three runs visible (Run 1, Run 2, Run 3). Each has distinctly different gate-level netlist diagrams with different arrangements of logic gates. The bottom text reads: "Different gates. Different wiring. Every time."

## Verdict: PASS

## Severity: N/A

## Notes
- Excellent match to the script. Same Verilog source producing three visibly different netlists is clearly demonstrated.
- The "SAME VERILOG SOURCE" label, three separate "SYNTHESIS" boxes, and three distinct netlist diagrams (Run 1, Run 2, Run 3) perfectly convey non-deterministic synthesis.
- The gate-level diagrams use standard logic gate symbols, adding technical credibility.
- The text "Different gates. Different wiring. Every time." reinforces the message.
- Note: The green checkmark / "Functionally equivalent" text may appear slightly after the t=107s mark (likely in V11's time range), which is a reasonable scene boundary choice.
