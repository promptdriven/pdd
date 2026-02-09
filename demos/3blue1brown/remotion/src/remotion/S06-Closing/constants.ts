import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Closing
// Audio: closing_narration.wav (33.5s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "So here's the mental shift."
//     2.7s [ 1] "You don't patch socks because socks got cheap."
//     5.6s [ 2] "The economics made patching irrational."
//     9.4s [ 3] "Code just got that cheap."
//    13.0s [ 4] "Prompts in code intent."
//    15.3s [ 5] "Tests preserve behavior."
//    17.4s [ 6] "Grounding maintains style."
//    20.7s [ 7] "Code is generated, verified, and disposable."
//    26.9s [ 8] "The code is just plastic."
//    30.5s [ 9] "The mold is what matters."

export const CLOSING_FPS = 30;
export const CLOSING_DURATION_SECONDS = 39;
export const CLOSING_DURATION_FRAMES = CLOSING_FPS * CLOSING_DURATION_SECONDS;
export const CLOSING_WIDTH = 1920;
export const CLOSING_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * CLOSING_FPS);

export const BEATS = {
  // Visual 0: CompleteSystem — "So here's the mental shift...."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(1.16),  // 35 frames

  // Visual 1: SockMetaphorFinal + "$0.50" overlay — "You don't patch socks..."
  VISUAL_01_START: s2f(2.7),  // 81 frames
  VISUAL_01_END: s2f(7.62),  // 229 frames

  // Visual 2: DeveloperRegenerates — "Code just got that cheap...."
  VISUAL_02_START: s2f(9.36),  // 281 frames
  VISUAL_02_END: s2f(10.74),  // 322 frames

  // Visual 3: ThreeComponents (triangle) — "Prompts encode intent...."
  VISUAL_03_START: s2f(13.02),  // 391 frames
  VISUAL_03_END: s2f(19.06),  // 572 frames

  // Visual 4: CodeRegenerationLoop — "Code is generated, verified, and disposable...."
  VISUAL_04_START: s2f(20.66),  // 620 frames
  VISUAL_04_END: s2f(24.66),  // 740 frames

  // Visual 5: CodeOutputMoldGlows — "The code is just plastic...."
  VISUAL_05_START: s2f(26.9),  // 807 frames
  VISUAL_05_END: s2f(33.22),  // 997 frames

  // Visual 6: FadeToBlack — title card after narration ends
  VISUAL_06_START: s2f(33.5),  // 1005 frames
  VISUAL_06_END: s2f(38.5),   // 1155 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "CompleteSystem", desc: "So here's the mental shift" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "SockMetaphorFinal", desc: "Don't patch socks, socks got cheap, irrational" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "DeveloperRegenerates", desc: "Code just got that cheap" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "ThreeComponents", desc: "Prompts encode intent, tests preserve, grounding maintains" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "CodeRegenerationLoop", desc: "Code is generated verified and disposable" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "CodeOutputMoldGlows", desc: "The code is just plastic, the mold is what matters" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "FadeToBlack", desc: "Title card and fade to black" },
];

// Props schema
export const ClosingSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultClosingSectionProps: z.infer<typeof ClosingSectionProps> = {
  showTitle: true,
};

export type ClosingSectionPropsType = z.infer<typeof ClosingSectionProps>;
