// Part1Economics18KeyInsightStillness — constants

// Background
export const BG_NEAR_BLACK = '#050810';

// Line
export const LINE_COLOR = '#334155';
export const LINE_OPACITY = 0.2;
export const LINE_Y = 540;
export const LINE_X_START = 400;
export const LINE_X_END = 1520;
export const LINE_CENTER_X = (LINE_X_START + LINE_X_END) / 2; // 960
export const LINE_WIDTH_PX = 1;

// Text
export const INSIGHT_TEXT = 'So let me put together what I just showed you.';
export const TEXT_COLOR = '#94A3B8';
export const TEXT_OPACITY = 0.6;
export const TEXT_Y = 500;
export const TEXT_FONT_SIZE = 20;
export const TEXT_FONT_WEIGHT = 400;
export const TEXT_FONT_FAMILY = 'Inter, system-ui, sans-serif';

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Timing (frames @ 30fps)
export const TOTAL_DURATION = 360;

// Phase 1: Clearing / darken (0–60)
export const CLEAR_START = 0;
export const CLEAR_DURATION = 60;

// Phase 2: Line draws from center outward (60–90)
export const LINE_DRAW_START = 60;
export const LINE_DRAW_DURATION = 30;

// Phase 3: Text fades in (90–150)
export const TEXT_FADE_IN_START = 90;
export const TEXT_FADE_IN_DURATION = 60;

// Phase 4: Hold / stillness (150–300) — no animation needed

// Phase 5: Text fades out (300–330), line holds
export const TEXT_FADE_OUT_START = 300;
export const TEXT_FADE_OUT_DURATION = 30;
