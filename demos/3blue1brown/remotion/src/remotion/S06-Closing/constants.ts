import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Closing
// Audio: closing_narration.wav (29.3s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "So here's the mental shit."
//     1.3s [ 1] "You don't patch socks because socks got cheap."
//     4.3s [ 2] "The economics made patching irrational."
//     8.6s [ 3] "Code just got that cheap."
//    11.0s [ 4] "Prompts in code intent."
//    13.3s [ 5] "Tests preserve behavior."
//    16.2s [ 6] "Grounding maintained style."
//    18.9s [ 7] "Code is generated, verified and disposable."
//    23.6s [ 8] "The code is just plastic."
//    27.0s [ 9] "The mold is what matters."

export const CLOSING_FPS = 30;
export const CLOSING_DURATION_SECONDS = 32;
export const CLOSING_DURATION_FRAMES = CLOSING_FPS * CLOSING_DURATION_SECONDS;
export const CLOSING_WIDTH = 1920;
export const CLOSING_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * CLOSING_FPS);

export const BEATS = {
  // Visual 0: CodeOutputMoldGlows — "So here's the mental shit...."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(9.66),  // 290 frames

  // Visual 1: ThreeComponents — "Prompts in code intent...."
  VISUAL_01_START: s2f(11.02),  // 331 frames
  VISUAL_01_END: s2f(17.82),  // 535 frames

  // Visual 2: CodeOutputMoldGlows — "Code is generated, verified and disposable...."
  VISUAL_02_START: s2f(18.92),  // 568 frames
  VISUAL_02_END: s2f(29.04),  // 871 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "CodeOutputMoldGlows", desc: "Mental shift: socks cheap, code cheap" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "ThreeComponents", desc: "Prompts encode intent, tests, grounding" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "CodeOutputMoldGlows", desc: "Code disposable, mold is what matters" },
];

// Props schema
export const ClosingSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultClosingSectionProps: z.infer<typeof ClosingSectionProps> = {
  showTitle: true,
};

export type ClosingSectionPropsType = z.infer<typeof ClosingSectionProps>;
