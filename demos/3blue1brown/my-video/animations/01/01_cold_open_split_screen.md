# Animation 01: Cold Open Split Screen

**Section:** Cold Open
**Timestamp:** 0:00 - 0:38
**Duration:** ~38 seconds
**Type:** Split screen with synchronized action

---

## Overview

The opening animation establishes the video's central metaphor by showing two parallel activities side-by-side:
- A modern developer using AI-assisted coding (Cursor)
- A 1950s grandmother darning a wool sock

Both complete their "patching" tasks simultaneously, then we zoom out to reveal the accumulated burden of all that careful repair work.

---

## Scene Structure

### Beat 1: Establish Split Screen (0:00 - 0:08)

**Layout:**
- Clean vertical divide at center of frame
- LEFT HALF: Modern, cool-toned (slight blue cast)
- RIGHT HALF: Warm, sepia-toned (amber/golden lamplight)

**Left Side - Developer:**
- Modern desk setup, minimal and clean
- Monitor displaying Cursor IDE interface
- Developer's hands on keyboard, face partially visible
- Code visible on screen with a function containing a bug
- Cursor's AI diff UI appearing (the characteristic green/red inline diff)

**Right Side - Grandmother:**
- 1950s domestic setting
- Wooden chair, small side table
- Oil lamp or early electric lamp casting warm light
- Elderly woman's hands holding darning egg and needle
- Wool sock stretched over darning egg, visible hole
- Thread and needle mid-stitch

**Camera:** Static, both sides framed identically (medium shot focusing on hands/work)

---

### Beat 2: Synchronized Task Completion (0:08 - 0:15)

**Left Side - The Edit:**
1. Cursor AI suggestion appears (green highlighted code)
2. Developer presses Tab or Enter to accept
3. Code smoothly replaces/inserts
4. Syntax highlighting updates
5. Brief "success" indicator (checkmark or green flash)

**Right Side - The Stitch:**
1. Needle pulls thread through fabric
2. Cross-stitch pattern forming over hole
3. Thread tightens, closing gap
4. Final stitch completes
5. Thread is cut with small scissors

**Timing:** Both actions complete at EXACTLY the same moment (0:15)

**Audio sync point:** Soft "click" or resolution tone as both complete

---

### Beat 3: Brief Satisfaction (0:15 - 0:18)

**Left Side:**
- Subtle nod or satisfied posture shift from developer
- Cursor shows clean, patched code
- Perhaps a brief file save animation

**Right Side:**
- Grandmother holds up sock briefly, inspecting
- Satisfied expression
- Sets sock aside

**Duration:** Short beat - just enough to register completion

---

### Beat 4: The Zoom Out - Revelation (0:18 - 0:32)

This is the key moment. We pull back to reveal the true scope.

**Left Side Zoom Out:**
1. Start: Single file with the patched function
2. Pull back: File tree appears - dozens of files
3. Continue: More files, diff markers visible throughout
4. Reveal: Massive codebase visualization
   - Files scattered/stacked
   - Red diff markers everywhere
   - TODO comments floating: `// FIXME`, `// temporary`, `// don't touch`
   - Git blame colors showing patchwork history
   - Perhaps a dependency graph with tangled lines

**Right Side Zoom Out:**
1. Start: The single repaired sock
2. Pull back: Side table has a small pile of mended items
3. Continue: Drawer opens or basket revealed
4. Reveal: Dozens of carefully mended garments
   - Socks with multiple patch areas
   - Shirts with elbow patches
   - Trousers with knee reinforcements
   - Each item showing accumulated repair history

**Camera Movement:**
- Smooth dolly zoom (Hitchcock-style) or simple pull-back
- Both sides zoom at identical rates
- Maintain split-screen divide throughout

**Visual Emphasis:**
- Slight vignette darkening on edges
- The "weight" of accumulation should feel heavy
- Colors slightly desaturate as scope increases

---

### Beat 5: Hold on Accumulated Weight (0:32 - 0:38)

**Static hold** on the zoomed-out view showing both accumulated repair histories.

**Left Side Final Frame:**
- Codebase visualization showing complexity
- Subtle animation: occasional flicker of a lint warning, a new TODO appearing
- The developer small in frame, surrounded by their patchwork

**Right Side Final Frame:**
- The mending basket/collection
- Perhaps grandmother's hands resting, slightly tired
- Warm but heavy atmosphere

**Narrator line during this beat:**
> "But here's what your great-grandmother figured out sixty years ago."

---

## Technical Specifications

### Resolution & Format
- **Aspect Ratio:** 16:9
- **Resolution:** 4K (3840x2160) recommended, 1080p minimum
- **Frame Rate:** 60fps for smooth zooms, can be 30fps for static portions

### Color Palette

| Element | Hex Code | Usage |
|---------|----------|-------|
| Left BG (Modern) | #1a1a2e | Dark, cool workspace |
| Left Accent | #4A90D9 | Cursor UI elements |
| Right BG (1950s) | #2d2416 | Warm, amber shadows |
| Right Accent | #D9944A | Lamplight, warmth |
| Divider | #ffffff | Clean vertical line, 2px |
| Code (normal) | #e0e0e0 | Standard code text |
| Code (patch) | #4ade80 | Added/fixed code |
| Code (removed) | #f87171 | Deleted code |

### Typography

**Code (Left Side):**
- Font: JetBrains Mono or SF Mono
- Size: Readable at 4K, approximately 14-16pt equivalent
- Line height: 1.5

**TODO/Comments:**
- Same monospace font
- Slightly muted color (#888)

### Cursor UI Accuracy

Reference actual Cursor interface:
- Dark theme (default)
- Inline diff presentation
- Green for additions, red for removals
- The characteristic "Accept" button or Tab indicator

---

## Animation Curves

All movements should use **ease-in-out-cubic** or similar smooth easing (3B1B signature style).

### Zoom Out Timing
```
0:18 - 0:20  Start zoom, slow ease-in
0:20 - 0:28  Main zoom, constant speed
0:28 - 0:32  Decelerate, ease-out to final frame
```

### Code Edit Animation
```
0:08 - 0:10  AI suggestion fades in
0:10 - 0:12  Highlight/selection appears
0:12 - 0:14  Code replacement animation
0:14 - 0:15  Success indicator
```

### Darning Animation
```
0:08 - 0:15  Continuous needle/thread motion
             (7-8 individual stitch cycles)
0:15        Thread cut, completion
```

---

## Asset Requirements

### Left Side (Developer)
- [ ] Cursor IDE mockup or screen recording
- [ ] Realistic code sample (Python or TypeScript recommended)
- [ ] Function with a believable bug being fixed
- [ ] File tree visualization for zoom-out
- [ ] Codebase complexity visualization (graph/scatter)
- [ ] Floating TODO/FIXME text elements

### Right Side (Grandmother)
- [ ] Period-appropriate room setting (can be illustrated or 3D)
- [ ] Darning egg prop
- [ ] Needle and thread animation
- [ ] Wool sock with visible hole → repaired
- [ ] Collection of mended garments for reveal
- [ ] Oil/electric lamp with warm light source

### Audio
- [ ] Soft keyboard typing (subtle, not prominent)
- [ ] Thread pulling through fabric (foley)
- [ ] Scissors snip
- [ ] Resolution tone at 0:15 sync point
- [ ] Ambient: Modern hum (left), period silence/clock tick (right)

---

## Manim Implementation Notes

If implementing in Manim/ManimGL:

```python
# Suggested scene structure
class ColdOpenSplitScreen(Scene):
    def construct(self):
        # Create split screen containers
        left_panel = Rectangle(width=7, height=8).shift(LEFT * 3.5)
        right_panel = Rectangle(width=7, height=8).shift(RIGHT * 3.5)
        divider = Line(UP * 4, DOWN * 4)

        # Beat 1: Establish
        self.play(FadeIn(left_panel), FadeIn(right_panel), Create(divider))

        # Beat 2: Synchronized completion
        # Use AnimationGroup with lag_ratio=0 for perfect sync

        # Beat 4: Zoom out
        # Use self.camera.frame.animate.scale() for smooth zoom
```

### Key Manim Considerations
- Use `VGroup` for each side to enable synchronized transforms
- `AnimationGroup` with `lag_ratio=0` for simultaneous actions
- Camera frame scaling for zoom effect
- Consider `ImageMobject` for realistic UI elements
- `SVGMobject` for iconography and simple graphics

---

## Storyboard Frames

### Frame 1 (0:00)
```
┌─────────────────┬─────────────────┐
│                 │                 │
│   [CURSOR IDE]  │  [LAMPLIGHT]    │
│                 │                 │
│   def parse():  │    ~~~○~~~     │
│     # bug here  │   (sock/egg)    │
│                 │                 │
│   [HANDS]       │   [HANDS]       │
│                 │                 │
└─────────────────┴─────────────────┘
```

### Frame 2 (0:15) - Completion
```
┌─────────────────┬─────────────────┐
│                 │                 │
│   [CURSOR IDE]  │  [LAMPLIGHT]    │
│       ✓         │       ✓         │
│   def parse():  │    ~~~●~~~     │
│     # fixed!    │   (repaired)    │
│                 │                 │
│   [satisfied]   │   [satisfied]   │
│                 │                 │
└─────────────────┴─────────────────┘
```

### Frame 3 (0:32) - Zoomed Out
```
┌─────────────────┬─────────────────┐
│ ┌──┐┌──┐┌──┐    │                 │
│ │  ││  ││  │    │  ┌──┐ ┌──┐     │
│ └──┘└──┘└──┘    │  │~~│ │~~│     │
│   ┌──┐┌──┐      │  └──┘ └──┘     │
│   │  ││  │ //FIX│    ┌──┐        │
│   └──┘└──┘      │    │~~│ [basket]│
│ //TODO  ┌──┐    │    └──┘        │
│ [dev]   │  │    │         [gma]  │
└─────────────────┴─────────────────┘
```

---

## Transition to Next Scene

At 0:38, this scene transitions to:

**Hard cut** to modern day - person discovering hole in sock, shrugging, tossing it in trash, grabbing fresh pair from multi-pack.

The transition should feel abrupt - a deliberate contrast to the careful, accumulated repair work just shown.

---

## Checklist

- [ ] Split screen layout finalized
- [ ] Left side Cursor UI mockup complete
- [ ] Right side 1950s setting designed
- [ ] Code sample written (realistic bug fix)
- [ ] Darning animation reference gathered
- [ ] Zoom-out codebase visualization designed
- [ ] Zoom-out mending collection designed
- [ ] Audio assets listed and sourced
- [ ] Timing locked to narration
- [ ] Manim scene structure drafted
- [ ] Color grading defined for both sides
