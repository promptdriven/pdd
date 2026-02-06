import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 5: Compound Returns
// Audio: part5_compound_narration.wav (63.5s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "Let's talk about compound returns."
//     3.1s [ 1] "When you patch code, each fix has local returns."
//     7.3s [ 2] "You fixed one bug in one place."
//     9.5s [ 3] "Similar bugs can still occur elsewhere."
//    12.4s [ 4] "And sometimes your patch introduces new bugs."
//    16.0s [ 5] "The returns are linear at best."
//    18.6s [ 6] "Often sub-linear."
//    21.9s [ 7] "When you add a test in PDD, the returns are different."
//    26.2s [ 8] "That test you wrote today"
//    27.7s [ 9] "it constrains tomorrow's generation"
//    30.0s [10] "and next week's and next years"
//    31.9s [11] "it's a permanent wall."
//    34.4s [12] "Every investment in the mold has compound returns."
//    37.9s [13] "Every investment in patching has diminishing returns."
//    42.9s [14] "Your great-grandmother wasn't stupid for darning socks."
//    47.0s [15] "The economics made it rational."
//    50.0s [16] "And you're not stupid for patching code."
//    52.9s [17] "Until now the economics made it rational"
//    55.6s [18] "but the economics changed"
//    57.0s [19] "and when economics changed,"
//    59.3s [20] "behavior that was rational becomes darning socks."

export const PART5_FPS = 30;
export const PART5_DURATION_SECONDS = 66;
export const PART5_DURATION_FRAMES = PART5_FPS * PART5_DURATION_SECONDS;
export const PART5_WIDTH = 1920;
export const PART5_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART5_FPS);

export const BEATS = {
  // Visual 0: GraphAnimateCurve — "Let's talk about compound returns...."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(19.68),  // 590 frames

  // Visual 1: ShortPromptTests — "When you add a test in PDD, the returns are differ..."
  VISUAL_01_START: s2f(21.88),  // 656 frames
  VISUAL_01_END: s2f(33.5),  // 1005 frames

  // Visual 2: BothGenerateFinal — "Every investment in the mold has compound returns...."
  VISUAL_02_START: s2f(34.42),  // 1033 frames
  VISUAL_02_END: s2f(40.66),  // 1220 frames

  // Visual 3: veo:07_split_screen_sepia — "Your great-grandmother wasn't stupid for darning s..."
  VISUAL_03_START: s2f(42.86),  // 1286 frames
  VISUAL_03_END: s2f(55.56),  // 1667 frames

  // Visual 4: CodeOutputMoldGlows — "but the economics changed..."
  VISUAL_04_START: s2f(55.56),  // 1667 frames
  VISUAL_04_END: s2f(63.04),  // 1891 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "GraphAnimateCurve", desc: "Patch returns: local, linear, sub-linear" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "ShortPromptTests", desc: "PDD returns: test constrains all future, permanent" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "BothGenerateFinal", desc: "Compound vs diminishing returns" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "veo:07_split_screen_sepia", desc: "Great-grandmother/you: economics was rational" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "CodeOutputMoldGlows", desc: "Economics changed, darning socks" },
];

// Props schema
export const Part5CompoundReturnsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart5CompoundReturnsProps: z.infer<typeof Part5CompoundReturnsProps> = {
  showTitle: true,
};

export type Part5CompoundReturnsPropsType = z.infer<typeof Part5CompoundReturnsProps>;
