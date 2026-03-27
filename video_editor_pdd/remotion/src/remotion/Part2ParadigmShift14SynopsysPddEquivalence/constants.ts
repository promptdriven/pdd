// ── Canvas ──────────────────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 390;
export const BG_COLOR = "#0A0F1A";

// ── Blueprint Grid ──────────────────────────────────────────────────
export const GRID_SPACING = 60;
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.03;

// ── Colors ──────────────────────────────────────────────────────────
export const SYNOPSYS_ACCENT = "#4A90D9";
export const PDD_ACCENT = "#D9944A";
export const BODY_TEXT_COLOR = "#E2E8F0";
export const ARROW_COLOR = "#64748B";
export const CONNECTING_LINE_COLOR = "#5AAA6E";
export const CONNECTING_LINE_OPACITY = 0.4;
export const SUBTITLE_COLOR = "#94A3B8";
export const SUBTITLE_OPACITY = 0.6;

// ── Typography ──────────────────────────────────────────────────────
export const FONT_FAMILY = "Inter, sans-serif";
export const LINE_FONT_SIZE = 32;
export const SUBTITLE_FONT_SIZE = 18;

// ── Layout ──────────────────────────────────────────────────────────
export const LINE1_Y = 440;
export const LINE2_Y = 520;
export const SUBTITLE_Y = 600;
export const CENTER_X = 960;

// ── Animation Timing (frames) ───────────────────────────────────────
export const LINE1_START = 0;
export const LINE1_END = 60;
export const LINE2_START = 60;
export const LINE2_END = 120;
export const CONNECTING_START = 120;
export const CONNECTING_END = 180;
export const SUBTITLE_START = 180;
export const SUBTITLE_FADE_DURATION = 30;
export const HOLD_START = 240;
export const HOLD_END = 330;
export const FADEOUT_START = 330;
export const FADEOUT_DURATION = 60;

// ── Typewriter ──────────────────────────────────────────────────────
export const CHAR_DELAY_FRAMES = 2;

// ── Line Data ───────────────────────────────────────────────────────
export interface TextSegment {
  text: string;
  color: string;
  fontWeight: number;
}

export const LINE1_SEGMENTS: TextSegment[] = [
  { text: "Synopsys: ", color: SYNOPSYS_ACCENT, fontWeight: 700 },
  { text: "specification in → verified hardware out.", color: BODY_TEXT_COLOR, fontWeight: 400 },
];

export const LINE2_SEGMENTS: TextSegment[] = [
  { text: "PDD: ", color: PDD_ACCENT, fontWeight: 700 },
  { text: "prompt in → verified software out.", color: BODY_TEXT_COLOR, fontWeight: 400 },
];
