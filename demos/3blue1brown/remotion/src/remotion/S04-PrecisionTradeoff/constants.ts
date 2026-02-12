import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 4: Precision Tradeoff
// Audio: part4_precision_narration.wav (58.8s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "Here's something subtle that changes how you think abou..."
//     4.4s [ 1] "In 3D printing, there's no mold."
//     6.8s [ 2] "The machine must know exactly where to place every sing..."
//    11.5s [ 3] "The specification must be extremely precise."
//    15.7s [ 4] "In injection molding, precision comes from the walls."
//    19.6s [ 5] "The material just flows until it's constrained."
//    23.4s [ 6] "This maps directly to PDD."
//    26.7s [ 7] "With few tests, your prompt needs to specify everything..."
//    30.4s [ 8] "edge cases, error handling, exact behavior in every sit..."
//    35.3s [ 9] "With many tests, the prompt only needs to specify inten..."
//    40.0s [10] "The tests handle the constraints."
//    43.1s [11] "This is why test accumulation matters."
//    46.0s [12] "It's not just about catching bugs."
//    48.2s [13] "It's about making prompts simpler and regeneration safe..."
//    52.8s [14] "The more walls you have, the less you need to specify."
//    56.9s [15] "The mold does the precision work."

export const PART4_FPS = 30;
export const PART4_DURATION_SECONDS = 61;
export const PART4_DURATION_FRAMES = PART4_FPS * PART4_DURATION_SECONDS;
export const PART4_WIDTH = 1920;
export const PART4_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART4_FPS);

export const BEATS = {
  // Visual 0: veo:split_3d_vs_mold — "Here's something subtle that changes how you think..."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(3.02),  // 91 frames

  // Visual 1: PrinterFocus — "In 3D printing, there's no mold...."
  VISUAL_01_START: s2f(4.4),  // 132 frames
  VISUAL_01_END: s2f(14.46),  // 434 frames

  // Visual 2: MoldFlowFocus — "In injection molding, precision comes from the wal..."
  VISUAL_02_START: s2f(15.68),  // 470 frames
  VISUAL_02_END: s2f(22.12),  // 664 frames

  // Visual 3: PrecisionGraph — "This maps directly to PDD...."
  VISUAL_03_START: s2f(23.42),  // 703 frames
  VISUAL_03_END: s2f(25.76),  // 773 frames

  // Visual 4: LongPrompt — "With few tests, your prompt needs to specify every..."
  VISUAL_04_START: s2f(26.72),  // 802 frames
  VISUAL_04_END: s2f(34.64),  // 1039 frames

  // Visual 5: ShortPromptTests — "With many tests, the prompt only needs to specify ..."
  VISUAL_05_START: s2f(35.28),  // 1058 frames
  VISUAL_05_END: s2f(42.0),  // 1260 frames

  // Visual 6: GraphAnimateCurve — "This is why test accumulation matters...."
  VISUAL_06_START: s2f(43.14),  // 1294 frames
  VISUAL_06_END: s2f(52.02),  // 1561 frames

  // Visual 7: BothGenerateFinal — "The more walls you have, the less you need to spec..."
  // Extended to fill remaining section duration (was 58.58s, now 61s).
  VISUAL_07_START: s2f(52.8),  // 1584 frames
  VISUAL_07_END: s2f(61.0),   // 1830 frames — fills to end of section
};

// Visual sequence: maps BEATS ranges to composition IDs
//
// NOTE: The spec (README.md) lists GraphAnimateCurve (4.5) right after
// PrecisionGraph (4.4). However, the audio narration locks a different order:
//   - 26.7s "With few tests, specify everything..." -> LongPrompt
//   - 35.3s "With many tests, only needs intent..." -> ShortPromptTests
//   - 43.1s "Test accumulation matters..."          -> GraphAnimateCurve
// The narration first shows concrete examples (dense prompt, then short prompt
// with tests), then zooms out to the abstract curve. This order is correct for
// the audio sync; rearranging would mismatch narration content with visuals.
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo:split_3d_vs_mold", desc: "Something subtle that changes how you think about prompts" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "PrinterFocus", desc: "3D printing no mold, every point precise, specification prec" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "MoldFlowFocus", desc: "Injection molding precision comes from walls, flows constrai" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "PrecisionGraph", desc: "This maps directly to PDD" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "LongPrompt", desc: "Few tests prompt specifies everything, edge cases, errors" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "ShortPromptTests", desc: "Many tests prompt only needs intent, tests handle constraint" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "GraphAnimateCurve", desc: "Test accumulation not just catching bugs, simpler prompts" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "BothGenerateFinal", desc: "More walls less to specify, mold does precision work" },
];

// Props schema
export const Part4PrecisionTradeoffProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart4PrecisionTradeoffProps: z.infer<typeof Part4PrecisionTradeoffProps> = {
  showTitle: true,
};

export type Part4PrecisionTradeoffPropsType = z.infer<typeof Part4PrecisionTradeoffProps>;
