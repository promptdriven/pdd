# Veo Prompt: Cold Open Split Screen

## Primary Prompt

```
Split screen video, vertical divider in center.

LEFT SIDE: Modern software developer at minimalist desk, dark room with cool blue monitor glow, hands typing on keyboard, computer screen showing code editor with dark theme, making a small edit to code, satisfied subtle nod when complete.

RIGHT SIDE: 1950s elderly woman in warm lamplight, cozy domestic interior, sitting in wooden chair, hands carefully darning a wool sock stretched over a darning egg, needle and thread weaving through fabric, warm amber lighting from oil lamp, gentle focused expression, completes repair and briefly inspects work.

Both sides complete their tasks at exactly the same moment. Synchronized timing.

Camera slowly pulls back on both sides simultaneously to reveal: LEFT shows dozens of code files and complex software project, RIGHT shows basket full of mended clothes and repaired garments.

Cinematic, smooth camera movement, 4K quality, photorealistic, soft focus on backgrounds, sharp focus on hands and work.
```

---

## Segmented Prompts (For Better Control)

### Segment 1: Establish Split Screen (0:00 - 0:08)

```
Split screen with clean vertical white line divider in center of frame.

LEFT HALF: Modern software developer workspace, dark minimalist desk setup, single monitor glowing with blue-tinted code editor interface, developer's hands positioned on mechanical keyboard, dark theme IDE showing Python code with a function visible, cool color temperature, contemporary office aesthetic.

RIGHT HALF: 1950s cozy domestic interior, elderly grandmother sitting in worn wooden chair beside small side table, warm amber glow from antique oil lamp, hands holding wooden darning egg with wool sock stretched over it, visible hole in sock heel, needle threaded with yarn ready to begin repair, sepia warm tones, nostalgic period-accurate setting.

Static camera, medium shot framing both subjects identically, both focused on their respective tasks. Cinematic lighting, shallow depth of field, photorealistic, 4K.
```

### Segment 2: Synchronized Task Completion (0:08 - 0:15)

```
Split screen continuous from previous shot.

LEFT SIDE: Developer's fingers tap keyboard, code editor shows green highlighted text appearing (AI code suggestion), developer presses key to accept, code smoothly updates on screen, small checkmark or success indicator appears briefly, developer gives subtle satisfied micro-expression.

RIGHT SIDE: Grandmother's weathered hands guide needle and thread through sock fabric in steady rhythm, cross-stitch pattern slowly closing the hole, thread pulled taut with each pass, final stitch completed, small scissors snip thread, grandmother holds up repaired sock briefly examining her work with quiet satisfaction.

Both tasks complete at precisely the same moment - synchronized parallel action. Smooth continuous motion, photorealistic hands and movements, warm right side cool left side color contrast maintained.
```

### Segment 3: The Reveal Zoom Out (0:18 - 0:32)

```
Split screen continuous, camera begins slow cinematic pull-back zoom on both sides simultaneously.

LEFT SIDE REVEALS: Zooming out from single code file to show massive software project - dozens of file icons and code windows scattered across screen, red and green diff markers visible throughout, floating text comments reading "TODO" and "FIXME" and "temporary fix", complex tangled dependency lines connecting files, overwhelming accumulation of patches and fixes, developer now small in frame surrounded by digital complexity.

RIGHT SIDE REVEALS: Zooming out from single sock to show overflowing mending basket - dozens of carefully repaired garments piling up, socks with multiple visible patch areas, shirts with elbow patches, trousers with reinforced knees, drawer or basket full of accumulated repair work, grandmother now small in frame surrounded by lifetime of careful mending.

Smooth dolly zoom out, both sides moving at identical pace, maintaining split screen divide, sense of weight and accumulation on both sides, slightly melancholic tone, the burden of endless repair work visible. Cinematic, 4K, photorealistic.
```

### Segment 4: Hold on Accumulated Weight (0:32 - 0:38)

```
Split screen final wide shot, static camera hold.

LEFT: Full view of complex software codebase visualization, files and patches everywhere, subtle flickering of new warnings appearing, developer small figure amid digital chaos, cool blue corporate lighting.

RIGHT: Full view of mending collection and domestic workspace, basket overflowing with repaired garments, grandmother's tired but proud posture, warm lamp glow now seeming insufficient for the scale of work, golden hour nostalgic feeling.

Static hold, both sides showing the accumulated weight of careful repair work over time, contemplative mood, slight vignette darkening at edges, photorealistic, cinematic color grading.
```

---

## Style Modifiers

Add these to any prompt for consistent style:

```
Style: Cinematic documentary, photorealistic, 4K resolution, 24fps film look, shallow depth of field, professional color grading, smooth camera movements, inspired by educational YouTube videos like 3Blue1Brown and Kurzgesagt, clean compositions, thoughtful pacing.
```

```
Lighting: LEFT side cool blue monitor glow with dark ambient, RIGHT side warm amber tungsten lamp light with soft shadows, strong color temperature contrast between sides.
```

```
Mood: Contemplative, slightly melancholic, the weight of accumulated work, parallel between old and new, neither side judged negatively, both showing dedication to craft.
```

---

## Negative Prompts

```
Avoid: Fast cuts, shaky camera, harsh lighting, cluttered compositions, cartoonish style, anime, low resolution, text overlays, watermarks, stock footage feel, overly dramatic, action movie style.
```

---

## Technical Settings

| Parameter | Recommended Value |
|-----------|-------------------|
| Aspect Ratio | 16:9 |
| Resolution | 4K (2160p) or 1080p |
| Duration | 8-10 seconds per segment |
| Frame Rate | 24fps (cinematic) |
| Style Preset | Cinematic / Documentary |

---

## Shot-by-Shot Prompts (Shortest Form)

If Veo works better with very concise prompts:

**Shot 1:**
```
Split screen, left: developer typing code in dark room with blue monitor glow, right: 1950s grandmother darning sock by warm lamplight, both working intently, static medium shot, cinematic, photorealistic
```

**Shot 2:**
```
Split screen continuous, left: code edit completes with green highlight, developer nods, right: grandmother finishes final stitch and snips thread, both complete simultaneously, synchronized moment, cinematic
```

**Shot 3:**
```
Split screen slow zoom out, left reveals massive codebase with dozens of files and TODO comments, right reveals basket full of mended clothes, both sides showing accumulated repair work, cinematic dolly out, melancholic tone
```

**Shot 4:**
```
Split screen wide shot hold, left: developer small amid complex code visualization, right: grandmother small amid piles of mended garments, weight of accumulated work visible on both sides, contemplative, static camera, cinematic
```

---

## Image-to-Video Alternative

If generating a starting frame first works better:

**Starting Frame Prompt (for image generation):**
```
Split screen photograph, vertical white line divider. Left half: modern software developer at desk, blue monitor glow, hands on keyboard, code visible on screen, dark minimal office. Right half: 1950s grandmother in wooden chair, warm oil lamp light, hands holding darning egg with sock, needle and thread visible. Both subjects in identical medium shot framing. Cinematic, photorealistic, 4K, shallow depth of field.
```

Then use image-to-video with motion prompt:
```
Both subjects complete their work simultaneously - left side code updates, right side stitching finishes. Then camera slowly zooms out on both sides to reveal accumulated work. Smooth cinematic movement.
```

---

## Notes for Best Results

1. **Generate segments separately** - Veo handles shorter clips better than long continuous shots
2. **Maintain consistency** - Use the same style modifiers across all segments
3. **The sync moment is key** - The simultaneous completion at 0:15 is the emotional beat
4. **Color contrast matters** - Cool blue left, warm amber right creates visual storytelling
5. **Zoom should feel weighted** - The reveal should feel like "oh no, look at all this"
6. **May need compositing** - True split screen might require generating sides separately and combining in post
