import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 4: Precision Tradeoff
// Audio: part4_precision_narration.wav (61.5s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "Here's something subtle that changes how you think abou..."
//     5.0s [ 1] "In 3D printing, there's no mold."
//     7.3s [ 2] "The machine must know exactly where to place every sing..."
//    11.8s [ 3] "The specification must be extremely precise."
//    15.8s [ 4] "In injection molding, precision comes from the walls."
//    19.3s [ 5] "The material just flows until it's constrained."
//    23.8s [ 6] "This maps directly to PDD."
//    27.0s [ 7] "With few tests, your prompt needs to specify everything..."
//    32.2s [ 8] "Edge cases, error handling, exact behavior in every sit..."
//    38.0s [ 9] "With many tests, the prompt only needs to specify inten..."
//    42.7s [10] "The tests handle the constraints."
//    45.9s [11] "This is why test accumulation matters."
//    49.6s [12] "It's not just about catching bugs."
//    51.4s [13] "It's about making prompts simpler and regeneration safe..."
//    57.2s [14] "More tests, less prompt."
//    59.6s [15] "The walls do the precision work."

export const PART4_FPS = 30;
export const PART4_DURATION_SECONDS = 64;
export const PART4_DURATION_FRAMES = PART4_FPS * PART4_DURATION_SECONDS;
export const PART4_WIDTH = 1920;
export const PART4_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART4_FPS);

export const BEATS = {
  // Visual 0: veo:split_3d_vs_mold — "Here's something subtle that changes how you think..."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(3.24),  // 97 frames

  // Visual 1: PrinterFocus — "In 3D printing, there's no mold...."
  VISUAL_01_START: s2f(5.04),  // 151 frames
  VISUAL_01_END: s2f(14.24),  // 427 frames

  // Visual 2: MoldFlowFocus — "In injection molding, precision comes from the wal..."
  VISUAL_02_START: s2f(15.84),  // 475 frames
  VISUAL_02_END: s2f(21.44),  // 643 frames

  // Visual 3: PrecisionGraph — "This maps directly to PDD...."
  VISUAL_03_START: s2f(23.8),  // 714 frames
  VISUAL_03_END: s2f(26.02),  // 781 frames

  // Visual 4: LongPrompt — "With few tests, your prompt needs to specify every..."
  VISUAL_04_START: s2f(26.96),  // 809 frames
  VISUAL_04_END: s2f(37.22),  // 1117 frames

  // Visual 5: ShortPromptTests — "With many tests, the prompt only needs to specify ..."
  VISUAL_05_START: s2f(37.98),  // 1139 frames
  VISUAL_05_END: s2f(44.22),  // 1327 frames

  // Visual 6: GraphAnimateCurve — "This is why test accumulation matters...."
  VISUAL_06_START: s2f(45.9),  // 1377 frames
  VISUAL_06_END: s2f(56.38),  // 1691 frames

  // Visual 7: BothGenerateFinal — "More tests, less prompt...."
  VISUAL_07_START: s2f(57.2),  // 1716 frames
  VISUAL_07_END: s2f(61.38),  // 1841 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo:split_3d_vs_mold", desc: "Something subtle about prompts" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "PrinterFocus", desc: "3D printing: no mold, every point, precise" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "MoldFlowFocus", desc: "Injection molding: walls constrain the flow" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "PrecisionGraph", desc: "This maps directly to PDD" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "LongPrompt", desc: "Few tests: specify everything" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "ShortPromptTests", desc: "Many tests: specify intent only" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "GraphAnimateCurve", desc: "Test accumulation makes prompts simpler" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "BothGenerateFinal", desc: "More tests less prompt, walls do precision" },
];

// Props schema
export const Part4PrecisionTradeoffProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart4PrecisionTradeoffProps: z.infer<typeof Part4PrecisionTradeoffProps> = {
  showTitle: true,
};

export type Part4PrecisionTradeoffPropsType = z.infer<typeof Part4PrecisionTradeoffProps>;
