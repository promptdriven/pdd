import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 4: Precision Tradeoff
// Audio: part4_precision_narration.wav (60.4s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "Your great-grandmother wasn't stupid for darning socks."
//     4.1s [ 1] "The economics made it rational."
//     6.9s [ 2] "And you're not stupid for patching code."
//    10.0s [ 3] "Until now, the economics made it rational,"
//    12.9s [ 4] "but the economics changed."
//    14.5s [ 5] "And when economics change, behavior that was rational b..."
//    19.3s [ 6] "Darning socks."
//    22.3s [ 7] "Almana."
//    23.5s [ 8] "Ugh."
//    25.0s [ 9] "One more thing."
//    26.4s [10] "This transition doesn't eliminate developers."
//    28.4s [11] "It elevates them."
//    31.2s [12] "Mole designers need deeper understanding than wood carv..."
//    35.0s [13] "They need to understand materials,"
//    37.3s [14] "physics, tolerances, failure modes."
//    41.4s [15] "PDD developers work at the level of specification."
//    44.7s [16] "You're not writing the defensive code."
//    46.7s [17] "You're specifying what defensive behavior looks like."
//    50.0s [18] "You're not implementing the error handling."
//    52.6s [19] "You're defining the contract it must satisfy."
//    54.8s [20] "The shift from implementation craft to specification cr..."

export const PART4_FPS = 30;
export const PART4_DURATION_SECONDS = 63;
export const PART4_DURATION_FRAMES = PART4_FPS * PART4_DURATION_SECONDS;
export const PART4_WIDTH = 1920;
export const PART4_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART4_FPS);

export const BEATS = {
  // Visual 0: veo:07_split_screen_sepia — "Your great-grandmother wasn't stupid for darning s..."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(5.66),  // 170 frames

  // Visual 1: GraphAnimateCurve — "And you're not stupid for patching code...."
  VISUAL_01_START: s2f(6.94),  // 208 frames
  VISUAL_01_END: s2f(20.16),  // 605 frames

  // Visual 2: BothGenerateFinal — "Almana...."
  VISUAL_02_START: s2f(22.26),  // 668 frames
  VISUAL_02_END: s2f(23.82),  // 715 frames

  // Visual 3: CrossSectionIntro — "One more thing...."
  VISUAL_03_START: s2f(25.02),  // 751 frames
  VISUAL_03_END: s2f(39.72),  // 1192 frames

  // Visual 4: PromptGovernsCode — "PDD developers work at the level of specification...."
  VISUAL_04_START: s2f(41.38),  // 1241 frames
  VISUAL_04_END: s2f(60.28),  // 1808 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo:07_split_screen_sepia", desc: "Grandmother: not stupid → economics rational" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "GraphAnimateCurve", desc: "You: not stupid → economics changed → became darning socks" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "BothGenerateFinal", desc: "Transition beat" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "CrossSectionIntro", desc: "Doesn't eliminate → elevates → mold designers → materials → " },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "PromptGovernsCode", desc: "PDD developers → specification level → not writing → specify" },
];

// Props schema
export const Part4PrecisionTradeoffProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart4PrecisionTradeoffProps: z.infer<typeof Part4PrecisionTradeoffProps> = {
  showTitle: true,
};

export type Part4PrecisionTradeoffPropsType = z.infer<typeof Part4PrecisionTradeoffProps>;
