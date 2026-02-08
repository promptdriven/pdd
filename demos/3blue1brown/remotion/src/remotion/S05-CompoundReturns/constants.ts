import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 5: Compound Returns
// Audio: part5_compound_narration.wav (84.9s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "Let's talk about compound returns."
//     2.7s [ 1] "When you patch code, each fix has local returns."
//     6.8s [ 2] "You fixed one bug in one place."
//     9.1s [ 3] "Similar bugs can still occur elsewhere,"
//    11.6s [ 4] "and sometimes your patch introduces new bugs."
//    14.8s [ 5] "CodeRabbit found AI patches carry 1.7 times more issues"
//    19.0s [ 6] "than human code."
//    20.9s [ 7] "So each patch risks creating more patches."
//    24.4s [ 8] "The returns are linear at best, often sub-linear,"
//    29.3s [ 9] "and the cost keeps compounding."
//    31.2s [10] "CISQ estimates technical debt costs US companies $1.52 ..."
//    39.0s [11] "When you add a test in PDD, the returns are different."
//    43.3s [12] "That test you wrote today, it constrains tomorrow's gen..."
//    48.0s [13] "and next week's, and next years, it's a permanent wall."
//    53.9s [14] "Every investment in the mold has compound returns."
//    57.4s [15] "Every investment in patching has diminishing returns."
//    62.3s [16] "Your great-grandmother wasn't stupid for darning socks."
//    66.3s [17] "The economics made it rational."
//    68.5s [18] "And you're not stupid for patching code."
//    71.2s [19] "Until now, the economics made it rational."
//    76.4s [20] "But the economics changed, and when economics change,"
//    80.4s [21] "behavior that was rational becomes..."
//    83.8s [22] "darning socks."

export const PART5_FPS = 30;
export const PART5_DURATION_SECONDS = 87;
export const PART5_DURATION_FRAMES = PART5_FPS * PART5_DURATION_SECONDS;
export const PART5_WIDTH = 1920;
export const PART5_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART5_FPS);

export const BEATS = {
  // Visual 0: CompoundCurvesGraph phase 1 — "Let's talk about compound returns...."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(1.86),  // 56 frames

  // Visual 1: CompoundCurvesGraph phase 2 — "When you patch code, each fix has local returns...."
  VISUAL_01_START: s2f(2.74),  // 82 frames
  VISUAL_01_END: s2f(23.56),  // 707 frames

  // Visual 2: CompoundCurvesGraph phase 3 — "The returns are linear at best, often sub-linear,..."
  VISUAL_02_START: s2f(24.42),  // 733 frames
  VISUAL_02_END: s2f(37.34),  // 1120 frames

  // Visual 3: CompoundCurvesGraph phase 5 — "When you add a test in PDD, the returns are differ..."
  VISUAL_03_START: s2f(39.04),  // 1171 frames
  VISUAL_03_END: s2f(52.28),  // 1568 frames

  // Visual 4: InvestmentTable — "Every investment in the mold has compound returns...."
  VISUAL_04_START: s2f(53.94),  // 1618 frames
  VISUAL_04_END: s2f(60.32),  // 1810 frames

  // Visual 5: veo:07_split_screen_sepia — "Your great-grandmother wasn't stupid for darning s..."
  VISUAL_05_START: s2f(62.34),  // 1870 frames
  VISUAL_05_END: s2f(67.66),  // 2030 frames

  // Visual 6: veo:07_split_screen_sepia — "And you're not stupid for patching code...."
  VISUAL_06_START: s2f(68.5),  // 2055 frames
  VISUAL_06_END: s2f(73.92),  // 2218 frames

  // Visual 7: CrossingPoint — "But the economics changed, and when economics chan..."
  VISUAL_07_START: s2f(76.38),  // 2291 frames
  VISUAL_07_END: s2f(84.5),  // 2535 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "CompoundCurvesGraph:1", desc: "Let's talk about compound returns" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "CompoundCurvesGraph:2", desc: "Patch code local returns, 1.7x issues, risks more patches" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "CompoundCurvesGraph:3", desc: "Returns linear at best, cost compounding, 1.52T annually" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "CompoundCurvesGraph:5", desc: "PDD test returns compound, constrains future, permanent wall" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "InvestmentTable", desc: "Every mold investment compounds, patching diminishes" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "veo:07_split_screen_sepia", desc: "Great-grandmother rational for darning, economics made sense" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "veo:07_split_screen_sepia", desc: "Not stupid for patching, economics made it rational" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "CrossingPoint", desc: "Economics changed, rational becomes darning socks" },
];

// Props schema
export const Part5CompoundReturnsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart5CompoundReturnsProps: z.infer<typeof Part5CompoundReturnsProps> = {
  showTitle: true,
};

export type Part5CompoundReturnsPropsType = z.infer<typeof Part5CompoundReturnsProps>;
