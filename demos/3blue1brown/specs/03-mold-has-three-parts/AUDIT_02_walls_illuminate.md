# Audit: 02_walls_illuminate.md

## Spec Summary
The walls of the mold illuminate fully in amber with specific test labels appearing on each wall segment: "null → None", "empty string → ''", "handles unicode", "latency < 100ms". Each label appears sequentially with wall pulse effects.

## Implementation Status
Implemented

## Deltas Found

### Wall Configuration Mismatch
- **Spec says**: Four wall segments (Top, Right, Bottom, Left) with one label each
- **Implementation does**: Three wall segments (Left, Right, Bottom) only - no top wall shown
- **Severity**: High - Missing the top wall entirely

### Label Content Different
- **Spec says**: 4 specific labels:
  - Top: "null → None"
  - Right: "empty string → ''"
  - Bottom: "handles unicode"
  - Left: "latency < 100ms"
- **Implementation does**: 6 different labels (constants.ts lines 33-40):
  - "null → None" ✓
  - "empty → None"
  - '"abc" → "abc"'
  - '" abc " → "abc"'
  - '"a1b2" → "a1b2"'
  - '"a@b" → None'
- **Severity**: High - Only 1 of 4 specified labels present, content is different

### Label Positioning
- **Spec says**: One label per wall (4 total)
- **Implementation does**: Left wall has 3 labels, right wall has 3 labels (lines 97-148)
- **Severity**: Medium - Different layout pattern

### Missing Wall Pulse on Label Appearance
- **Spec says**: "Each wall segment pulses as the word 'walls' is emphasized" and individual wall pulses as each label appears
- **Implementation does**: Walls have static glow, no per-label pulse animation
- **Severity**: Medium - Missing interactive visual feedback

### Wall Pulse Timing Missing
- **Spec says**: Sequential timing for each wall (frames 60-120-180-240 for labels)
- **Implementation does**: All labels stagger from frame 90 with 30-frame intervals, but no wall-specific pulses
- **Severity**: Low - Labels animate but walls don't pulse individually

### Section Title Text Different
- **Spec says**: No specific title mentioned, just focus on walls
- **Implementation does**: Adds "First: tests" with subtitle "The Constraints" (lines 163-181)
- **Severity**: Low - Addition provides context

### Caption Text Different
- **Spec says**: No caption specified
- **Implementation does**: "Tests define the boundaries. Code must fit within them." (lines 184-199)
- **Severity**: Low - Addition, not contradiction

## Missing Elements
- No connecting lines from labels to wall segments (spec line 52)
- No top wall with "null → None" label
- "empty string → ''" label missing
- "handles unicode" label missing
- "latency < 100ms" label missing
- No individual wall pulse effect synchronized with label appearance
