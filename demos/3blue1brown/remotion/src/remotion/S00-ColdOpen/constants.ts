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
export const COLD_OPEN_DURATION_SECONDS = 54;
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

  // Visual 1B: Hold on accumulated weight (01e) — 6-second static hold
  // Spec: 0:32-0:38 mapped to production timeline. Contemplative beat where
  // the viewer absorbs the full scope of accumulated work on both sides.
  VISUAL_01B_START: s2f(7.72),  // 232 frames — immediately after zoom-out
  VISUAL_01B_END: s2f(13.72),  // 412 frames — 6 seconds of hold

  // Visual 2: veo:cold_open_01f_modern_sock_toss — "60 years ago, when Sox got cheap enough, she stopp..."
  VISUAL_02_START: s2f(14.26),  // 428 frames
  VISUAL_02_END: s2f(18.5),  // 555 frames

  // Visual 3: code_blinks:01f — "Code just got that cheap...."
  // Spec 01f: ~10-second contemplative beat — full-frame patched code with blinking cursor.
  // Static hold so the viewer absorbs accumulated technical debt before hard cut to regeneration.
  VISUAL_03_START: s2f(18.78),  // 563 frames
  VISUAL_03_END: s2f(28.78),   // 863 frames — 10 seconds (300 frames at 30fps)

  // Visual 3B: code_regenerates:01g — Code deletion + empty beat + regeneration
  // Spec 01g: ~15-second sequence (1:35-1:50). Seven animation phases:
  //   selection flash (0.2s) -> delete sweep (0.8s) -> empty beat (1s) ->
  //   terminal activity (0.2s) -> line-by-line regeneration (0.8s) ->
  //   terminal completion (0.2s) -> hold on clean code (11.8s).
  // "The empty beat is critical -- do not rush it." (visual thesis)
  // Narration "So why are we still patching?" lands during hold on clean code.
  // Crossfades into title card in final portion.
  VISUAL_03B_START: s2f(28.78),  // 863 frames — immediately after 01f
  VISUAL_03B_END: s2f(43.78),   // 1313 frames — 15 seconds (450 frames at 30fps)

  // Visual 4: title_over_code:Prompt-Driven Development — "So why are we still patching?..."
  // Spec: ~10 seconds. Code dims 0-2s, title fades 1-3s, hold 3-9s, prep 9-10s.
  VISUAL_04_START: s2f(43.78),  // 1313 frames
  VISUAL_04_END: s2f(53.78),   // 1613 frames — 10 seconds for contemplative title card
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo:cold_open_01a_establish", desc: "If you use Cursor, Claude Code, Copilot, getting good" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "veo:cold_open_01d_zoom_out", desc: "Great-grandmother figured out sixty years ago" },
  { start: BEATS.VISUAL_01B_START, end: BEATS.VISUAL_01B_END, id: "remotion:cold_open_01e_hold", desc: "Hold on accumulated weight — contemplative 6s beat" },
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
