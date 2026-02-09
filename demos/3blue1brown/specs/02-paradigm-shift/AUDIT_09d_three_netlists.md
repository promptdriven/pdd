# Audit: 09d_three_netlists.md

## Spec Summary
Same Verilog code runs through synthesis three times, producing three visibly different gate-level netlists side by side. Green checkmarks appear over each with "Functionally Equivalent" label, demonstrating non-deterministic generation with deterministic verification. Duration: ~20 seconds.

## Implementation Status
**Implemented** - Split across ChipDesignHistory's "threeNetlists" and "verification" phases.

## Deltas Found

### Verilog Code Source Display
- **Spec says**: "Verilog code visible at top, centered" with "Subtle blue-ish glow to suggest it holds the value" (lines 21-25, sketch at lines 50-68)
- **Implementation does**: Compact Verilog code block at top with glowing property (ChipDesignHistory.tsx:926-936), positioned at x=580, y=40, scale=0.85
- **Severity**: None - Correctly implemented with glow

### "Same input" Label
- **Spec says**: Implied by visual layout showing same code feeding three runs
- **Implementation does**: Explicit label "Same Verilog Source" rendered (ChipDesignHistory.tsx:940-956)
- **Severity**: None - Enhancement improves clarity

### Three Synthesis Runs
- **Spec says**: "Same compiler icon appears three times (or one icon runs three times)" with "Run 1", "Run 2", "Run 3" labels (lines 27-30)
- **Implementation does**: No visible synthesis tool icons for the three runs, but netlists are labeled "Run 1", "Run 2", "Run 3" (ChipDesignHistory.tsx:977-1007)
- **Severity**: Medium - Missing the visual synthesis process for each run

### Three Netlists with Different Layouts
- **Spec says**: Three netlists with visibly different gate arrangements (lines 122-140):
  - Netlist A: AND gates first, linear left-to-right, compact
  - Netlist B: OR gates first, tree-like branching, spread vertically
  - Netlist C: Mixed ordering, diagonal wiring, uses NAND/NOR equivalents
- **Implementation does**: Three netlists rendered with variants A, B, C using NETLIST_LAYOUTS data structure (ChipDesignHistory.tsx:970-1008, GateNetlist:331-397)
- **Severity**: None - Correctly implemented with distinct layouts

### Netlist Drawing Animation
- **Spec says**: Staggered drawing of three netlists (lines 76-102) with different start times
- **Implementation does**: Three netlists draw with interpolated progress at different frame ranges (RUN1: 60-150, RUN2: 150-240, RUN3: 240-330) (ChipDesignHistory.tsx:843-875)
- **Severity**: None - Correctly implemented

### Flow Arrows from Code to Netlists
- **Spec says**: "Arrow/flow from code to left slot," "center slot," "right slot" (lines 82-97)
- **Implementation does**: Three flow arrows rendered from code position to each netlist (ChipDesignHistory.tsx:959-967)
- **Severity**: None - Correctly implemented

### "Different every time" Label
- **Spec says**: Not explicitly specified in structured overlay, but implied by narration
- **Implementation does**: Label "Different gates. Different wiring. Every time." rendered at bottom during hold phase (ChipDesignHistory.tsx:1011-1035)
- **Severity**: None - Good addition for narrative clarity

### Verification Checkmarks
- **Spec says**: "Green checkmark (#5AAA6E) appears over Netlist 1, Then over Netlist 2 (0.5s delay), Then over Netlist 3 (0.5s delay)" with "scale bounce" animation (lines 106-115, 141-184)
- **Implementation does**: VerificationCheckmark component with spring animation and staggered delays (ChipDesignHistory.tsx:400-449, verification phase:1138-1160). Uses CHECK_GREEN color and spring config matching spec.
- **Severity**: None - Correctly implemented in separate verification phase

### "Functionally Equivalent" Label
- **Spec says**: "Text fades in below all three netlists" in green (#5AAA6E) with "Connecting line or bracket groups all three" (lines 117-120)
- **Implementation does**: Label rendered with green border, background, and detailed styling including "Formal equivalence checking via SAT/SMT solvers" subtitle (ChipDesignHistory.tsx:1163-1201)
- **Severity**: None - Enhanced implementation with additional context

### Checkmark Component Details
- **Spec says**: Detailed VerificationCheckmark component with spring animation (lines 143-184)
- **Implementation does**: Component structure matches spec with spring damping=12, stiffness=200, mass=0.5 (ChipDesignHistory.tsx:400-449)
- **Severity**: None - Correctly implemented

### Netlist Positioning
- **Spec says**: Three netlists "Side by side in the lower two-thirds of screen" (line 35)
- **Implementation does**: Netlists positioned at y=580 (threeNetlists phase) and y=500 (verification phase) with x positions at 200, 850, 1500 (ChipDesignHistory.tsx:918-921, 1053-1056)
- **Severity**: None - Correctly positioned

### Gate Symbol Variations
- **Spec says**: Specific gate types and layouts for each netlist variant (lines 122-140)
- **Implementation does**: NETLIST_LAYOUTS constant (in constants file) defines gate positions and types for variants A, B, C. GateSymbol component renders AND, OR, NOT, NAND, NOR gates (ChipDesignHistory.tsx:267-327)
- **Severity**: None - Correctly implemented

## Missing Elements

### Synthesis Tool Icons for Three Runs
- **Spec says**: "Same compiler icon appears three times (or one icon runs three times)" with visual indicators for each run (lines 27-30)
- **Implementation does**: No synthesis tool boxes visible during the three-netlists phase
- **Severity**: Medium - The visual process of running synthesis three times is not shown, only the outputs

### Slight Pulsing on Differences
- **Spec says**: "Optional: subtle pulsing on the differences" during the hold phase (lines 105-107)
- **Implementation does**: No pulsing animation on the netlists themselves
- **Severity**: Low - Marked as optional

### Connecting Bracket/Line for Equivalence
- **Spec says**: "Connecting line or bracket groups all three" netlists under the Functionally Equivalent label (line 119)
- **Implementation does**: Label is centered but no explicit visual grouping element
- **Severity**: Low - The centered position and color scheme sufficiently indicate grouping

## Notes

The implementation splits this spec across two phases:
1. **threeNetlists phase**: Shows the three different netlists being generated from the same Verilog source
2. **verification phase**: Adds the green checkmarks and "Functionally Equivalent" label

This is a logical separation that maintains the narrative flow. The implementation is highly faithful to the spec with proper:
- Three distinct netlist layouts (variants A, B, C)
- Staggered animation timing
- Spring-animated checkmarks with proper delays
- Green color coding for verification (#5AAA6E)
- Detailed labeling and context

The main gap is the absence of visible synthesis tool processing for each of the three runs, which would strengthen the visual metaphor of "running synthesis multiple times."

---

## Resolution Status

**Date:** 2026-02-08
**Status:** RESOLVED

### Changes Made

1. **Added Synthesis Tool Boxes for Three Runs**: Modified the ThreeNetlistsPhase component to include three SynthesisToolBox components, one above each netlist position.

2. **Implemented Visual Processing**:
   - Each synthesis tool appears with fade-in animation when its respective run starts
   - Rotating gear animation indicates active processing
   - Tools positioned at y=410, above netlists at y=580
   - Each tool has independent opacity control (synth1Opacity, synth2Opacity, synth3Opacity)

3. **Updated Flow Arrows**:
   - Added flow arrows from Verilog code to each synthesis tool
   - Added flow arrows from each synthesis tool to its respective netlist
   - Creates complete visual pipeline: Code → Synth Tool → Netlist (3x)

### Severity Resolution

- **Medium: Missing Synthesis Tool Icons for Three Runs** - RESOLVED: Three synthesis tools now visible, one per run
- **Low: Missing Slight Pulsing on Differences** - NOT IMPLEMENTED: Marked as optional in spec
- **Low: Missing Connecting Bracket/Line for Equivalence** - ACCEPTED: Centered label position provides sufficient visual grouping

### Implementation Details

The synthesis tools use the existing SynthesisToolBox component with proper positioning and timing:
- Run 1 tool appears at frame 60 (THREE_NETLISTS_BEATS.RUN1_START)
- Run 2 tool appears at frame 150 (THREE_NETLISTS_BEATS.RUN2_START)
- Run 3 tool appears at frame 240 (THREE_NETLISTS_BEATS.RUN3_START)

Each tool shows rotating gear animation while processing, making it clear that synthesis is running three separate times on the same input, producing three different outputs. This strengthens the visual metaphor of non-deterministic generation.
