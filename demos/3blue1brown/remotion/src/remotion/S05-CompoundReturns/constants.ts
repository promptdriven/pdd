import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 5: Compound Returns
// Audio: part5_compound_narration.wav (38.2s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "The code is still there. It's still complex, but you do..."
//     5.1s [ 1] "You live in the specification. The code is generated, v..."
//    13.4s [ 2] "Heather just spread case."
//    15.7s [ 3] "So here's the mental shit. You don't patch socks becaus..."
//    20.3s [ 4] "The economics made patching irrational."
//    24.6s [ 5] "Code just got that cheap prompts in code intent."
//    29.3s [ 6] "Tests preserve behavior."
//    32.5s [ 7] "Grounding maintained style."
//    35.1s [ 8] "Code is generated, verified, and disposable."

export const PART5_FPS = 30;
export const PART5_DURATION_SECONDS = 41;
export const PART5_DURATION_FRAMES = PART5_FPS * PART5_DURATION_SECONDS;
export const PART5_WIDTH = 1920;
export const PART5_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART5_FPS);

export const BEATS = {
  // Visual 0: CodeOutputMoldGlows — "The code is still there. It's still complex, but y..."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(11.76),  // 353 frames

  // Visual 1: CodeOutputMoldGlows — "Heather just spread case...."
  VISUAL_01_START: s2f(13.36),  // 401 frames
  VISUAL_01_END: s2f(14.8),  // 444 frames

  // Visual 2: CodeOutputMoldGlows — "So here's the mental shit. You don't patch socks b..."
  VISUAL_02_START: s2f(15.68),  // 470 frames
  VISUAL_02_END: s2f(28.34),  // 850 frames

  // Visual 3: ThreeComponents — "Tests preserve behavior...."
  VISUAL_03_START: s2f(29.3),  // 879 frames
  VISUAL_03_END: s2f(33.94),  // 1018 frames

  // Visual 4: CodeOutputMoldGlows — "Code is generated, verified, and disposable...."
  VISUAL_04_START: s2f(35.06),  // 1052 frames
  VISUAL_04_END: s2f(37.9),  // 1137 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "CodeOutputMoldGlows", desc: "Code still there → live in specification → verified disposab" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "CodeOutputMoldGlows", desc: "Transition" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "CodeOutputMoldGlows", desc: "Mental shift: don't patch socks → cheap → prompts encode int" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "ThreeComponents", desc: "Tests preserve behavior → grounding maintains style" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "CodeOutputMoldGlows", desc: "Code generated, verified, disposable" },
];

// Props schema
export const Part5CompoundReturnsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart5CompoundReturnsProps: z.infer<typeof Part5CompoundReturnsProps> = {
  showTitle: true,
};

export type Part5CompoundReturnsPropsType = z.infer<typeof Part5CompoundReturnsProps>;
