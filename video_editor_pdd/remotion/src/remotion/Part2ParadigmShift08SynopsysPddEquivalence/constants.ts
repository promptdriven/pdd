// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Background
export const BG_COLOR = "#0A0F1A";

// Colors — Synopsys row (cool blue)
export const SYNOPSYS_COLOR = "#4A90D9";
export const SYNOPSYS_OPACITY = 0.5;
export const SYNOPSYS_LABEL_OPACITY = 0.4;

// Colors — PDD row (warm amber)
export const PDD_COLOR = "#D9944A";
export const PDD_OPACITY = 0.5;
export const PDD_LABEL_OPACITY = 0.4;

// Colors — Shared
export const NEUTRAL_COLOR = "#94A3B8";
export const NEUTRAL_OPACITY = 0.4;
export const VERIFY_COLOR = "#5AAA6E";
export const VERIFY_OPACITY = 0.5;

export const ARROW_COLOR = "#475569";
export const ARROW_OPACITY = 0.3;

export const DASHED_LINE_COLOR = "#475569";
export const DASHED_LINE_OPACITY = 0.15;

export const TEXT_COLOR = "#E2E8F0";

// Typography
export const UI_FONT = "'Inter', sans-serif";
export const ROW_LABEL_SIZE = 12;
export const STAGE_LABEL_SIZE = 11;
export const EQUIV_SIZE = 64;
export const SUMMARY_SIZE = 16;

// Layout — Row positions
export const TOP_ROW_Y = 280;
export const BOTTOM_ROW_Y = 680;
export const CENTER_Y = 480;

// Layout — Stage X positions
export const STAGE_X = [260, 560, 860, 1160] as const;

// Layout — Row labels
export const ROW_LABEL_X = 80;

// Layout — Arrow
export const ARROW_LENGTH = 80;
export const ARROW_GAP = 60; // half of icon width, start/end offset from stage center

// Layout — Icons
export const DOC_ICON_W = 70;
export const DOC_ICON_H = 90;
export const GEAR_ICON_SIZE = 60;
export const CLUSTER_ICON_SIZE = 80;
export const SHIELD_ICON_W = 50;
export const SHIELD_ICON_H = 60;

// Animation timing (frames @ 30fps, total 360)
export const TOTAL_FRAMES = 360;

// Phase 1: Row labels
export const LABEL_FADE_START = 0;
export const LABEL_FADE_END = 20;

// Phase 2: Top row stages (frame 30–100)
export const TOP_ROW_START = 30;
export const STAGE_FADE_DURATION = 15;
export const STAGE_STAGGER = 15;
export const ARROW_DRAW_DURATION = 10;

// Phase 3: Bottom row stages (frame 100–170)
export const BOTTOM_ROW_START = 100;

// Phase 4: Dashed connections (frame 170–220)
export const DASHED_START = 170;
export const DASHED_DRAW_DURATION = 20;
export const DASHED_STAGGER = 10;

// Phase 5: Equivalence symbol (frame 220–260)
export const EQUIV_FADE_START = 220;
export const EQUIV_FADE_DURATION = 20;
export const EQUIV_PULSE_PERIOD = 40;
export const EQUIV_MIN_OPACITY = 0.3;
export const EQUIV_MAX_OPACITY = 0.6;

// Phase 6: Summary text (frame 260–310)
export const SUMMARY_FADE_START = 260;
export const SUMMARY_FADE_DURATION = 20;
export const SUMMARY_Y = 900;
