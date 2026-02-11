# Audit Briefs for S02-S06

Pre-prepared context for the critic to efficiently audit each remaining section.
Each section is broken into batches of 3-5 scenes for manageable audit chunks.

## Batch Breakdown Summary

| Section | Batches | Total Scenes | Duration |
|---------|---------|-------------|----------|
| S02 | 3 batches (A-C) | 14 scenes | ~180s |
| S03 | 5 batches (A-E) | 21 scenes | ~295s |
| S04 | 2 batches (A-B) | 8 scenes | ~61s |
| S05 | 2 batches (A-B) | 8 scenes | ~87s |
| S06 | 2 batches (A-B) | 7 scenes | ~39s |

---

## S02: Paradigm Shift

**Video:** `outputs/sections/part2_paradigm_shift.mp4` (46.8 MB, ~180s at 30fps)
**Script:** Lines 161-225 of `scripts/main_script.md` (PART 2: THE PARADIGM SHIFT, 6:30-10:30)
**Specs:** `specs/02-paradigm-shift/`
**Composition:** `remotion/src/remotion/S02-ParadigmShift/Part2ParadigmShift.tsx`
**Constants:** `remotion/src/remotion/S02-ParadigmShift/constants.ts`

### Visual Segments (14 total)
| # | Time | Component | Key Content |
|---|------|-----------|-------------|
| V0 | 0-8.4s | veo:01_factory_floor | Factory floor, injection molding machine |
| V1 | 10.2-17.9s | veo:02_mold_closeup | Liquid plastic flows into mold |
| V2 | 19.6-27.8s | PartsEject | Mold opens, parts eject, counter 1..10..100 |
| V3 | 29-33.2s | DefectDiscovered | Defect in molded part (Veo clip) |
| V4 | 33.9-40.4s | EngineerFixesMold | Engineer adjusts mold wall |
| V5 | 40.4-47.9s | PerfectParts | New parts eject, all perfect |
| V6 | 47.9-54.8s | ValueAura | Split screen: craftsman vs mold, glowing aura |
| V7 | 54.8-63.8s | PlasticRegenerates | Part dissolves, regenerates |
| V8 | 65.5-71s | veo:07_craftsman_vs_mold | Transition to 1980s electronics lab |
| V9 | 72.6-93.7s | ChipDesignHistory:verilogSynthesis | Hand-drawn schematic -> Verilog + Synopsys |
| V10 | 95.2-108.5s | ChipDesignHistory:threeNetlists | Three different netlists, all equivalent |
| V11 | 109.6-131.1s | ChipDesignHistory:verification | SAT/SMT solver verification proof |
| V12 | 132.7-155.2s | ChipDesignHistory:abstractionTimeline | Transistors->Schematics->RTL->Behavioral->NL timeline |
| V13 | 155.2-177s | PromptGeneratesCode | Prompt->Code->Tests, same transition for software |

### Batch Breakdown

**S02 Batch A: V0-V5 (0-47.9s) -- Factory + Mold Metaphor**
- V0 veo:01_factory_floor, V1 veo:02_mold_closeup, V2 PartsEject, V3 DefectDiscovered, V4 EngineerFixesMold, V5 PerfectParts
- Frames: t=5, t=14, t=25, t=31, t=37, t=44
- Script: "Pattern across industries... make mold once... fix the mold"

**S02 Batch B: V6-V8 (47.9-71s) -- Value Migration + Chip History Intro**
- V6 ValueAura, V7 PlasticRegenerates, V8 veo:07_craftsman_vs_mold
- Frames: t=50, t=60, t=68
- Script: "Value lives in specification... chip industry hit this wall"

**S02 Batch C: V9-V13 (72.6-177s) -- Chip Design History + Software Parallel**
- V9 verilogSynthesis, V10 threeNetlists, V11 verification, V12 abstractionTimeline, V13 PromptGeneratesCode
- Frames: t=80, t=100, t=120, t=145, t=165
- Script: "1980s drew gates by hand... Verilog... synthesis non-deterministic... same transition for software"

---

## S03: Mold Has Three Parts

**Video:** `outputs/sections/part3_mold.mp4` (38.2 MB, ~295s at 30fps)
**Script:** Lines 228-380 of `scripts/main_script.md` (PART 3: THE MOLD HAS THREE PARTS, 10:30-16:00)
**Specs:** `specs/03-mold-has-three-parts/`
**Composition:** `remotion/src/remotion/S03-MoldThreeParts/Part3MoldThreeParts.tsx`
**Constants:** `remotion/src/remotion/S03-MoldThreeParts/constants.ts`

### Visual Segments (21 total)
| # | Time | Component | Key Content |
|---|------|-----------|-------------|
| V0 | 0-12.3s | CrossSectionIntro | Cross-section mold, 3 regions highlight |
| V1 | 13.4-23.6s | WallsIlluminate | Walls light up with labels (null->None, etc.) |
| V2 | 23.6-52.1s | LiquidInjection | Liquid flows, hits walls, constrained |
| V3 | 53.6-67s | FocusSingleWall | Zoom into one constraint |
| V4 | 67-83.6s | BugDiscovered | Bug found, don't patch the code |
| V5 | 83.6-85s | AddTestWall | New wall added |
| V6 | 85-100s | CodeRegenerates | Code regenerates with new wall |
| V7 | 100-107.4s | RatchetTimelapse | Tests accumulate, mold gets precise |
| V8 | 108-117.6s | TraditionalVsPdd | Bug fix: one place vs everywhere |
| V9 | 117.6-138.8s | Z3SmtSidebar | SAT/SMT solvers, Z3 formal verification |
| V10 | 140.2-171.4s | Z3SmtSidebar | Z3 proves for all inputs |
| V11 | 171.4-187.8s | InjectionNozzle | Second: the prompt |
| V12 | 187.8-195.5s | PromptTextFlows | Prompt defines what and why |
| V13 | 195.5-203.5s | PromptVariations | Code flexible, contract fixed |
| V14 | 203.5-210.4s | PromptGovernsCode | Prompt 1/5 to 1/10 size |
| V15 | 211.7-249.7s | ContextWindowComparison | NL density vs code, token efficiency |
| V16 | 250.1-258s | GroundingPanel | Third: grounding |
| V17 | 259.2-264.6s | GroundingComparison | Learned from past generations |
| V18 | 264.6-276.5s | GroundingDatabase | Style, patterns, conventions |
| V19 | 278.5-286.3s | ThreeComponents | Triangle: prompt+tests+grounding |
| V20 | 286.3-295s | CodeOutputMoldGlows | Code is output, mold is what matters |

### Batch Breakdown

**S03 Batch A: V0-V2 (0-52.1s) -- Mold Intro + Tests as Walls**
- V0 CrossSectionIntro, V1 WallsIlluminate, V2 LiquidInjection
- Frames: t=6, t=15, t=25, t=40
- VERIFY: Easing.sin fix in WallsIlluminate (was Easing.sine, crashed at frame 403)
- Script: "Mold has three components... first tests... walls of your mold"

**S03 Batch B: V3-V7 (53.6-107.4s) -- Bug Discovery + Ratchet**
- V3 FocusSingleWall, V4 BugDiscovered, V5 AddTestWall, V6 CodeRegenerates, V7 RatchetTimelapse
- Frames: t=60, t=75, t=84, t=92, t=104
- Script: "Bug found... add a wall... code regenerates... tests accumulate"

**S03 Batch C: V8-V10 (108-171.4s) -- Traditional vs PDD + Z3/SMT**
- V8 TraditionalVsPdd, V9 Z3SmtSidebar, V10 Z3SmtSidebar (continued)
- Frames: t=112, t=125, t=150, t=165
- Script: "Traditional fix one place... SAT and SMT solvers... Z3 proves for all inputs"

**S03 Batch D: V11-V15 (171.4-249.7s) -- Prompt + Context Window**
- V11 InjectionNozzle, V12 PromptTextFlows, V13 PromptVariations, V14 PromptGovernsCode, V15 ContextWindowComparison
- Frames: t=180, t=192, t=200, t=207, t=230
- Script: "Second the prompt... defines what and why... NL density vs code"

**S03 Batch E: V16-V20 (250.1-295s) -- Grounding + Three Components**
- V16 GroundingPanel, V17 GroundingComparison, V18 GroundingDatabase, V19 ThreeComponents, V20 CodeOutputMoldGlows
- Frames: t=254, t=262, t=270, t=282, t=291
- Script: "Third grounding... prompt+tests+grounding... code is output, mold is what matters"

### Known Fix Applied
- `Easing.sine` -> `Easing.sin` in WallsIlluminate.tsx (lines 44, 142) and ResearchAnnotations.tsx (line 23). Verify no rendering errors around V1 (t=13.4s).

---

## S04: Precision Tradeoff

**Video:** `outputs/sections/part4_precision.mp4` (25 MB, ~61s at 30fps)
**Script:** Lines 382-420 of `scripts/main_script.md` (PART 4: THE PRECISION TRADEOFF, 16:00-17:00)
**Specs:** `specs/04-precision-tradeoff/`
**Composition:** `remotion/src/remotion/S04-PrecisionTradeoff/Part4PrecisionTradeoff.tsx`
**Constants:** `remotion/src/remotion/S04-PrecisionTradeoff/constants.ts`

### Visual Segments (8 total)
| # | Time | Component | Key Content |
|---|------|-----------|-------------|
| V0 | 0-3s | veo:split_3d_vs_mold | Split screen: 3D printer vs injection mold |
| V1 | 4.4-14.5s | PrinterFocus | 3D printer close-up, every point precise |
| V2 | 15.7-22.1s | MoldFlowFocus | Mold walls, material flows and constrained |
| V3 | 23.4-25.8s | PrecisionGraph | Axes appear: Tests vs Prompt Precision |
| V4 | 26.7-34.6s | LongPrompt | Dense prompt block (few tests) |
| V5 | 35.3-42s | ShortPromptTests | Short prompt + many test cards |
| V6 | 43.1-52s | GraphAnimateCurve | Inverse relationship curve animates |
| V7 | 52.8-58.6s | BothGenerateFinal | Both approaches generate, tests do precision |

### Batch Breakdown

**S04 Batch A: V0-V3 (0-25.8s) -- 3D Printing vs Molding**
- V0 veo:split_3d_vs_mold, V1 PrinterFocus, V2 MoldFlowFocus, V3 PrecisionGraph
- Frames: t=2, t=10, t=18, t=24
- Script: "3D printing no mold, every point precise... molding precision from walls"

**S04 Batch B: V4-V7 (26.7-58.6s) -- Prompt Precision Tradeoff**
- V4 LongPrompt, V5 ShortPromptTests, V6 GraphAnimateCurve, V7 BothGenerateFinal
- Frames: t=30, t=38, t=48, t=55
- Script: "Few tests specify everything... many tests only intent... test accumulation matters"

---

## S05: Compound Returns

**Video:** `outputs/sections/part5_compound.mp4` (11.9 MB, ~87s at 30fps)
**Script:** Lines 422-480 of `scripts/main_script.md` (PART 5: COMPOUND RETURNS, 17:00-18:30)
**Specs:** `specs/05-compound-returns/`
**Composition:** `remotion/src/remotion/S05-CompoundReturns/Part5CompoundReturns.tsx`
**Constants:** `remotion/src/remotion/S05-CompoundReturns/constants.ts`

### Visual Segments (8 total)
| # | Time | Component | Key Content |
|---|------|-----------|-------------|
| V0 | 0-1.9s | CompoundCurvesGraph:1 | Title/intro to compound returns |
| V1 | 2.7-23.6s | CompoundCurvesGraph:2 | Patching: local returns, 1.7x issues |
| V2 | 24.4-39.4s | CompoundCurvesGraph:3 | Linear/sub-linear returns, $1.52T |
| V3 | 39.4-52.3s | CompoundCurvesGraph:5 | PDD test returns compound, permanent wall |
| V4 | 53.9-60.3s | InvestmentTable | Mold compounds, patching diminishes |
| V5 | 62.3-67.7s | veo:07_split_screen_sepia | Great-grandmother rational for darning |
| V6 | 68.5-73.9s | veo:07_split_screen_sepia | Not stupid for patching, until now |
| V7 | 76.4-84.5s | CrossingPoint | Economics changed, rational becomes darning |

### Batch Breakdown

**S05 Batch A: V0-V4 (0-60.3s) -- Compound Curves + Investment Table**
- V0 CompoundCurvesGraph:1, V1 CompoundCurvesGraph:2, V2 CompoundCurvesGraph:3, V3 CompoundCurvesGraph:5, V4 InvestmentTable
- Frames: t=1, t=10, t=30, t=45, t=57
- Script: "Compound returns... patching local... PDD compound... investment table"

**S05 Batch B: V5-V7 (62.3-84.5s) -- Sepia Veo + CrossingPoint**
- V5 veo:07_split_screen_sepia, V6 veo:07_split_screen_sepia, V7 CrossingPoint
- Frames: t=65, t=71, t=80
- Script: "Great-grandmother rational... not stupid for patching... economics changed"

---

## S06: Closing

**Video:** `outputs/sections/closing.mp4` (6.1 MB, ~39s at 30fps)
**Script:** Lines 482-530 of `scripts/main_script.md` (CLOSING, 18:30-19:10)
**Specs:** `specs/06-closing/`
**Composition:** `remotion/src/remotion/S06-Closing/ClosingSection.tsx`
**Constants:** `remotion/src/remotion/S06-Closing/constants.ts`

### Visual Segments (7 total)
| # | Time | Component | Key Content |
|---|------|-----------|-------------|
| V0 | 0-1.2s | CompleteSystem | "So here's the mental shift" |
| V1 | 2.7-7.6s | SockMetaphorFinal | Don't patch socks, $0.50 overlay |
| V2 | 9.4-10.7s | DeveloperRegenerates | Code just got that cheap |
| V3 | 13-19.1s | ThreeComponents | Triangle: prompts, tests, grounding |
| V4 | 20.7-24.7s | CodeRegenerationLoop | Generated, verified, disposable |
| V5 | 26.9-33.2s | CodeOutputMoldGlows | Code is just plastic, mold matters |
| V6 | 33.5-38.5s | FadeToBlack | Title card, fade to black |

### Batch Breakdown

**S06 Batch A: V0-V3 (0-19.1s) -- Mental Shift + Triangle**
- V0 CompleteSystem, V1 SockMetaphorFinal, V2 DeveloperRegenerates, V3 ThreeComponents
- Frames: t=1, t=5, t=10, t=16
- Script: "Mental shift... don't patch socks... code got cheap... prompts tests grounding"

**S06 Batch B: V4-V6 (20.7-38.5s) -- Loop + Mold Glows + Fade**
- V4 CodeRegenerationLoop, V5 CodeOutputMoldGlows, V6 FadeToBlack
- Frames: t=22, t=30, t=36
- Script: "Generated verified disposable... code is plastic... mold is what matters... title card"
