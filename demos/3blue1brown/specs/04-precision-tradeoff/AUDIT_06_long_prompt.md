# Audit: 06_long_prompt.md

## Spec Summary
Displays a dense 50-line prompt file (`parser_v1.prompt`) with auto-scrolling to emphasize complexity. Only 2-3 test walls appear on the right side to show the lack of test coverage. The visual emphasizes that without tests, prompts must carry all precision burden.

## Implementation Status
Implemented

## Deltas Found

### Test wall count
- **Spec says**: "2-3 test walls" (line 31), shown as `count={3}` in code (line 186)
- **Implementation does**: `count={3}` (line 308)
- **Severity**: None - Matches

### Test wall positioning
- **Spec says**: `position={{ x: 1400, y: 350 }}` (line 187)
- **Implementation does**: `position={{ x: 1450, y: 350 }}` (line 310)
- **Severity**: Low - 50px horizontal difference

### Scroll calculation
- **Spec says**: `const visibleStart = Math.floor(scrollProgress * (lines.length - 20))` and shows 25 lines (line 211-212)
- **Implementation does**: `const totalScrollableLines = Math.max(0, lines.length - maxVisibleLines)` then `const visibleStart = Math.floor(scrollProgress * totalScrollableLines)` (lines 22-23, with maxVisibleLines = 25)
- **Severity**: Low - More defensive calculation but same behavior

### Container height
- **Spec says**: `height: 800` (line 220)
- **Implementation does**: `height: 850` (line 33)
- **Severity**: Low - 50px taller

### Content area height
- **Spec says**: `height: 700` (line 254)
- **Implementation does**: `height: 750` (line 76)
- **Severity**: Low - 50px taller to match container

### Font styling
- **Spec says**: `fontFamily: 'monospace'` (line 259)
- **Implementation does**: `fontFamily: "JetBrains Mono, monospace"` (line 89)
- **Severity**: Low - Specific monospace font specified

### Header font weight
- **Spec says**: No font weight specified for header text
- **Implementation does**: `fontWeight: "bold"` (line 54)
- **Severity**: Low - Enhancement

### Syntax highlighting
- **Spec says**: Three colors based on line start: `#` → `#4A90D9`, `-` → `#D9944A`, else → `rgba(255, 255, 255, 0.8)` (lines 261-263)
- **Implementation does**: Uses COLORS constants: `COLORS.HEADER_BLUE`, `COLORS.BULLET_ORANGE`, `COLORS.TEXT_GRAY` plus adds `fontWeight: isHeader ? "bold" : "normal"` (lines 91-98)
- **Severity**: Low - Uses constants and adds bold for headers

### Scroll indicator added
- **Spec says**: No scroll indicator mentioned
- **Implementation does**: Adds visual scrollbar with thumb position (lines 120-144)
- **Severity**: Low - Enhancement not in spec

### Line count badge positioning
- **Spec says**: Not shown in spec code examples
- **Implementation does**: Positioned at `left: 1150, top: 140` (line 222)
- **Severity**: Low - Specific positioning added

### Test walls have "test" label
- **Spec says**: No text inside walls
- **Implementation does**: Each wall contains a small "test" label (lines 185-193)
- **Severity**: Low - Enhancement

### Test wall size
- **Spec says**: `width: 40, height: 60` (line 303-304)
- **Implementation does**: `width: 50, height: 70` (line 174-175)
- **Severity**: Low - 25% larger walls

### Border radius on walls
- **Spec says**: `borderRadius: 4` (line 306)
- **Implementation does**: `borderRadius: 6` (line 177)
- **Severity**: Low - Slightly more rounded

### Caption text added
- **Spec says**: No caption mentioned
- **Implementation does**: Adds italic caption "With few tests, your prompt needs to specify everything." at bottom (lines 315-342)
- **Severity**: Low - Enhancement matching narration

### showTestWalls prop added
- **Spec says**: Walls always shown
- **Implementation does**: Conditional rendering with `showTestWalls` prop (lines 306-312)
- **Severity**: Low - Flexibility enhancement

## Resolution Status
- **Status**: RESOLVED
- **Changes Made**: No changes needed - low severity only
- **Remaining Issues**: None

## Missing Elements
None - all core requirements implemented.

## Additional Features
1. Scroll indicator visual feedback
2. "test" labels inside each wall
3. Caption text synchronized with narration
4. Optional test wall display via `showTestWalls` prop
5. JetBrains Mono font for better code readability
6. Bold header styling in prompt content
7. Uses BEATS and COLORS constants from external file
