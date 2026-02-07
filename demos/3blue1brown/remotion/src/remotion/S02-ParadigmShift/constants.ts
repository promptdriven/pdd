import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 2: Paradigm Shift
// Audio: part2_paradigm_shift_narration.wav (177.1s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "There's a pattern here that shows up across industries,..."
//     6.0s [ 1] "a deeper shift in how things are made."
//    10.2s [ 2] "Consider injection molding. Before it existed, you craf..."
//    15.7s [ 3] "After it, you designed molds."
//    19.6s [ 4] "Make the mold once, produce unlimited identical parts."
//    23.9s [ 5] "Refine the mold once, every future part improves automa..."
//    29.0s [ 6] "And when there's a defect, you don't patch individual p..."
//    33.9s [ 7] "You fix the mold, and that fix applies to every part yo..."
//    40.4s [ 8] "This is the real shift, not cheaper material, a migrati..."
//    47.9s [ 9] "In crafting, value lives in the object. You protect the..."
//    54.8s [10] "In molding, value lives in the specification, the mold,..."
//    61.5s [11] "disposable, regenerate it at will."
//    65.5s [12] "And it's not just plastics. The chip industry hit this ..."
//    72.6s [13] "In the 1980s, chip designers drew every gate by hand."
//    76.9s [14] "When transistor counts hit tens of thousands, they coul..."
//    81.6s [15] "So in 1985, they moved up from schematics to verilog, a..."
//    88.9s [16] "You described what you wanted the chip to do, and a syn..."
//    95.2s [17] "But here's the thing, synthesis was non-deterministic."
//    99.4s [18] "Run it twice, get different gates, different wiring, di..."
//   105.7s [19] "the output varied every single time."
//   109.6s [20] "What synopsis did was wrap a verification tool chain ar..."
//   114.7s [21] "Formal equivalence checking using SAT and SMT solvers t..."
//   121.4s [22] "that the output, whatever it looked like, behaved ident..."
//   126.4s [23] "The gates were different every time. The function was t..."
//   132.7s [24] "By 1990, most designs were still schematic based. By th..."
//   140.3s [25] "Today, all but the most trivial chips use HDL. Every ti..."
//   146.5s [26] "what the current abstraction could handle, the industry..."
//   151.0s [27] "The designer stopped specifying how and started specify..."
//   155.2s [28] "But this is that same transition for software."
//   161.7s [29] "The prompt is your mold, the code is just plastic, and ..."
//   169.7s [30] "the code is different every generation. But the tests l..."

export const PART2_FPS = 30;
export const PART2_DURATION_SECONDS = 180;
export const PART2_DURATION_FRAMES = PART2_FPS * PART2_DURATION_SECONDS;
export const PART2_WIDTH = 1920;
export const PART2_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART2_FPS);

export const BEATS = {
  // Visual 0: veo:01_factory_floor — "There's a pattern here that shows up across indust..."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(8.42),  // 253 frames

  // Visual 1: veo:02_mold_closeup — "Consider injection molding. Before it existed, you..."
  VISUAL_01_START: s2f(10.16),  // 305 frames
  VISUAL_01_END: s2f(17.88),  // 536 frames

  // Visual 2: PartsEject — "Make the mold once, produce unlimited identical pa..."
  VISUAL_02_START: s2f(19.58),  // 587 frames
  VISUAL_02_END: s2f(27.82),  // 835 frames

  // Visual 3: veo:veo_defect_discovered — "And when there's a defect, you don't patch individ..."
  VISUAL_03_START: s2f(29.02),  // 871 frames
  VISUAL_03_END: s2f(33.24),  // 997 frames

  // Visual 4: PerfectParts — "You fix the mold, and that fix applies to every pa..."
  VISUAL_04_START: s2f(33.86),  // 1016 frames
  VISUAL_04_END: s2f(38.62),  // 1159 frames

  // Visual 5: ValueAura — "This is the real shift, not cheaper material, a mi..."
  VISUAL_05_START: s2f(40.36),  // 1211 frames
  VISUAL_05_END: s2f(54.82),  // 1645 frames

  // Visual 6: PlasticRegenerates — "In molding, value lives in the specification, the ..."
  VISUAL_06_START: s2f(54.82),  // 1645 frames
  VISUAL_06_END: s2f(63.78),  // 1913 frames

  // Visual 7: veo:07_craftsman_vs_mold — "And it's not just plastics. The chip industry hit ..."
  VISUAL_07_START: s2f(65.54),  // 1966 frames
  VISUAL_07_END: s2f(71.0),  // 2130 frames

  // Visual 8: MoldToPrompt — "In the 1980s, chip designers drew every gate by ha..."
  VISUAL_08_START: s2f(72.58),  // 2177 frames
  VISUAL_08_END: s2f(93.7),  // 2811 frames

  // Visual 9: MoldToPrompt — "But here's the thing, synthesis was non-determinis..."
  VISUAL_09_START: s2f(95.24),  // 2857 frames
  VISUAL_09_END: s2f(108.52),  // 3256 frames

  // Visual 10: MoldToPrompt — "What synopsis did was wrap a verification tool cha..."
  VISUAL_10_START: s2f(109.62),  // 3289 frames
  VISUAL_10_END: s2f(131.12),  // 3934 frames

  // Visual 11: MoldToPrompt — "By 1990, most designs were still schematic based. ..."
  VISUAL_11_START: s2f(132.68),  // 3980 frames
  VISUAL_11_END: s2f(155.2),  // 4656 frames

  // Visual 12: PromptGeneratesCode — "But this is that same transition for software...."
  VISUAL_12_START: s2f(155.2),  // 4656 frames
  VISUAL_12_END: s2f(176.98),  // 5309 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo:01_factory_floor", desc: "Pattern across industries, deeper shift in how things made" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "veo:02_mold_closeup", desc: "Consider injection molding, crafted to designed molds" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "PartsEject", desc: "Make mold once, unlimited parts, refine once all improve" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "veo:veo_defect_discovered", desc: "When there's a defect, don't patch individual parts" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "PerfectParts", desc: "Fix the mold, fix applies to every future part" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "ValueAura", desc: "Real shift: migration of where value lives" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "PlasticRegenerates", desc: "Molding value in specification, disposable, regenerate" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "veo:07_craftsman_vs_mold", desc: "Not just plastics, chip industry hit this exact wall" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "MoldToPrompt", desc: "1980s drew gates by hand, moved to Verilog in 1985" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "MoldToPrompt", desc: "Synthesis non-deterministic, different gates every time" },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "MoldToPrompt", desc: "Synopsys wrapped verification, SAT/SMT proof, same function" },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "MoldToPrompt", desc: "By 1990 schematic, mid-90s half switched, all use HDL now" },
  { start: BEATS.VISUAL_12_START, end: BEATS.VISUAL_12_END, id: "PromptGeneratesCode", desc: "Same transition for software, prompt is mold, tests lock" },
];

// Props schema
export const Part2ParadigmShiftProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart2ParadigmShiftProps: z.infer<typeof Part2ParadigmShiftProps> = {
  showTitle: true,
};

export type Part2ParadigmShiftPropsType = z.infer<typeof Part2ParadigmShiftProps>;
