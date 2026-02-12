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
export const COLD_OPEN_DURATION_SECONDS = 24;
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
  VISUAL_01_END: s2f(8.22),  // 247 frames — extended 0.5s for crossfade overlap

  // Visual 1B: Hold on accumulated weight (01e) — 3.5-second contemplative hold
  // Shortened from 6s to 2s to avoid absorbing narration segments 2-3.
  VISUAL_01B_START: s2f(7.72),  // 232 frames — immediately after zoom-out
  VISUAL_01B_END: s2f(11.22),   // 337 frames — 3.5 seconds of hold

  // Visual 2: veo:cold_open_01f_modern_sock_toss — "60 years ago, when Sox got cheap enough, she stopp..."
  // Realigned to play during segment 2 narration (8.3-12.8s) instead of segment 4.
  VISUAL_02_START: s2f(10.0),   // 300 frames — during segment 2
  VISUAL_02_END: s2f(12.52),    // 376 frames — ends before segment 3

  // Visual 3: code_blinks:01f — "Code just got that cheap...."
  // Shortened from 10s to 2s — brief visual punctuation during segment 3.
  VISUAL_03_START: s2f(12.80),  // 384 frames
  VISUAL_03_END: s2f(14.80),    // 444 frames — 2 seconds (60 frames at 30fps)

  // Visual 3B: code_regenerates:01g — Code deletion + empty beat + regeneration
  // Shortened from 15s to 5s (150 frames). Seven animation phases compressed.
  // Starts during segment 4 "So why are we still patching?" —
  // code deletion begins as the question is asked (powerful visual answer).
  VISUAL_03B_START: s2f(15.08),  // 452 frames
  VISUAL_03B_END: s2f(20.08),   // 602 frames — 5 seconds (150 frames at 30fps)

  // Visual 4: title_over_code:Prompt-Driven Development
  // Extended to fill remaining section (was 3s ending at 23.08, now ~4s ending at 24s).
  // Ensures no visual gap at end of section.
  VISUAL_04_START: s2f(20.08),  // 602 frames
  VISUAL_04_END: s2f(24.0),    // 720 frames — fills to end of section
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo:cold_open_01a_establish", desc: "If you use Cursor, Claude Code, Copilot, getting good" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "veo:cold_open_01d_zoom_out", desc: "Great-grandmother figured out sixty years ago" },
  { start: BEATS.VISUAL_01B_START, end: BEATS.VISUAL_01B_END, id: "remotion:cold_open_01e_hold", desc: "Hold on accumulated weight — contemplative 3.5s beat" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "veo:cold_open_01f_modern_sock_toss", desc: "When socks got cheap enough she stopped" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "code_blinks:01f", desc: "Code just got that cheap — contemplative patched code with blinking cursor" },
  { start: BEATS.VISUAL_03B_START, end: BEATS.VISUAL_03B_END, id: "code_regenerates:01g", desc: "Code regeneration — deletion, empty beat, line-by-line regen, title crossfade" },
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
