# AUDIT S03 V10 -- Z3SmtSidebar p2 (140.2s - 171.4s)

## Script Visual
"Side-by-side: Synopsys RTL=gates vs PDD+Z3 code satisfies spec. 'Mathematical proof, not testing.'"

## Frames Reviewed
- t=142s: Same sidebar layout as V9. Synopsys Formality (left) with checkmark, connecting line.
- t=155s: Full layout: Synopsys Formality + Z3 (Microsoft Research). Text: "Hardware: SMT-based formal proof", "PDD: SMT-based formal proof", "Same math."
- t=170s: Identical to t=155s -- layout holds steady during narration.

## Findings
- **PARTIAL**: The sidebar continues from V9 with the same Synopsys + Z3 layout
- **ISSUE**: Script calls for a distinct side-by-side showing "Synopsys Formality: SMT solver proves RTL = gates" (left) vs "PDD + Z3: SMT solver proves code satisfies spec" (right) with "Mathematical proof, not testing" label. The actual visual continues the V9 layout without transitioning to this more detailed comparison.
- **NOTE**: The "Mathematical proof, not testing" text is not explicitly shown. Instead "Same math." serves as the tagline.
- **MITIGATION**: The narration covers this content verbally while the visual reinforces the connection

## Verdict: PARTIAL PASS -- The side-by-side "RTL=gates vs code satisfies spec" detail and "Mathematical proof, not testing" label are missing from the visual. The scene holds the V9 layout throughout.
