import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Cold Open: The Sock Hook
// Audio: cold_open_narration.wav (16.1s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "If you use cursor or clawed code or copilot, you're get..."
//     5.2s [ 1] "But here's what your great-grandmother figured out."
//     8.3s [ 2] "60 years ago, when Sox got cheap enough, she stopped."
//    12.8s [ 3] "Code just got that cheap."
//    14.1s [ 4] "So why are we still patching?"

export const COLD_OPEN_FPS = 30;
export const COLD_OPEN_DURATION_SECONDS = 19;
export const COLD_OPEN_DURATION_FRAMES = COLD_OPEN_FPS * COLD_OPEN_DURATION_SECONDS;
export const COLD_OPEN_WIDTH = 1920;
export const COLD_OPEN_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * COLD_OPEN_FPS);

export const BEATS = {
  // Visual 0: veo:cold_open_01a_establish — "If you use cursor or clawed code or copilot, you'r..."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(4.92),  // 148 frames

  // Visual 1: veo:cold_open_01d_zoom_out — "But here's what your great-grandmother figured out..."
  VISUAL_01_START: s2f(5.24),  // 157 frames
  VISUAL_01_END: s2f(7.72),  // 232 frames

  // Visual 2: veo:cold_open_01f_modern_sock_toss — "60 years ago, when Sox got cheap enough, she stopp..."
  VISUAL_02_START: s2f(8.26),  // 248 frames
  VISUAL_02_END: s2f(12.5),  // 375 frames

  // Visual 3: code_regen:pdd generate — "Code just got that cheap...."
  VISUAL_03_START: s2f(12.78),  // 383 frames
  VISUAL_03_END: s2f(13.76),  // 413 frames

  // Visual 4: title_over_code:Prompt-Driven Development — "So why are we still patching?..."
  VISUAL_04_START: s2f(14.1),  // 423 frames
  VISUAL_04_END: s2f(15.96),  // 479 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo:cold_open_01a_establish", desc: "If you use Cursor, Claude Code, Copilot, getting good" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "veo:cold_open_01d_zoom_out", desc: "Great-grandmother figured out sixty years ago" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "veo:cold_open_01f_modern_sock_toss", desc: "When socks got cheap enough she stopped" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "code_regen:pdd generate", desc: "Code just got that cheap" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "title_over_code:Prompt-Driven Development", desc: "So why are we still patching" },
];

// Props schema
export const ColdOpenSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultColdOpenSectionProps: z.infer<typeof ColdOpenSectionProps> = {
  showTitle: true,
};

export type ColdOpenSectionPropsType = z.infer<typeof ColdOpenSectionProps>;
