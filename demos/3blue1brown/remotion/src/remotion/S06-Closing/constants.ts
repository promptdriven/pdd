import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Closing
// Audio: closing_narration.wav (7.0s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "The code is just plastic."
//     3.8s [ 1] "The mold is what matters."
//     6.4s [ 2] "Hmm."

export const CLOSING_FPS = 30;
export const CLOSING_DURATION_SECONDS = 9;
export const CLOSING_DURATION_FRAMES = CLOSING_FPS * CLOSING_DURATION_SECONDS;
export const CLOSING_WIDTH = 1920;
export const CLOSING_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * CLOSING_FPS);

export const BEATS = {
  // Visual 0: CodeOutputMoldGlows — "The code is just plastic...."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(1.68),  // 50 frames

  // Visual 1: ThreeComponents — "The mold is what matters...."
  VISUAL_01_START: s2f(3.8),  // 114 frames
  VISUAL_01_END: s2f(5.44),  // 163 frames

  // Visual 2: ThreeComponents — "Hmm...."
  VISUAL_02_START: s2f(6.44),  // 193 frames
  VISUAL_02_END: s2f(6.76),  // 203 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "CodeOutputMoldGlows", desc: "The code is just plastic" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "ThreeComponents", desc: "The mold is what matters" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "ThreeComponents", desc: "Hold" },
];

// Props schema
export const ClosingSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultClosingSectionProps: z.infer<typeof ClosingSectionProps> = {
  showTitle: true,
};

export type ClosingSectionPropsType = z.infer<typeof ClosingSectionProps>;
