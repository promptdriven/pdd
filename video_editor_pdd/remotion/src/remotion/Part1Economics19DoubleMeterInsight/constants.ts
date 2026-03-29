// ── Colors ──────────────────────────────────────────────────────
export const BG_DARK = "#050810";
export const BG_MAIN = "#0A0F1A";
export const TRACK_FILL = "#1E293B";
export const TRACK_BORDER = "#334155";
export const BLUE_FILL = "#4A90D9";
export const GREEN_FILL = "#5AAA6E";
export const LABEL_DIM = "#64748B";
export const TEXT_LIGHT = "#E2E8F0";
export const ACCENT_AND = "#F59E0B";

// ── Canvas ──────────────────────────────────────────────────────
export const CANVAS_W = 1920;
export const CANVAS_H = 1080;
export const TOTAL_FRAMES = 360;

// ── Meter Dimensions ────────────────────────────────────────────
export const METER_WIDTH = 80;
export const METER_HEIGHT = 600;
export const METER_RADIUS = 8;
export const LEFT_METER_X = 560;
export const RIGHT_METER_X = 1360;
export const METER_TOP_Y = 200;

// ── Animation Frames ────────────────────────────────────────────
export const BG_LIGHTEN_END = 30;
export const TRACK_DRAW_END = 30;
export const TITLES_START = 30;
export const TITLES_END = 60;
export const FILL_START = 60;
export const FILL_END = 180;
export const TOP_LABELS_START = 180;
export const TOP_LABELS_END = 210;
export const PULSE_START = 210;
export const PULSE_END = 270;
export const PULSE_CYCLE = 30;
export const INSIGHT_TEXT_START = 270;
export const INSIGHT_TEXT_END = 300;

// ── Meter Data ──────────────────────────────────────────────────
export const LEFT_METER_CONFIG = {
  title: "Effective Context Window",
  fillColor: BLUE_FILL,
  bottomLabel: "1×",
  topLabel: "5-10×",
  bottomFontSize: 18,
} as const;

export const RIGHT_METER_CONFIG = {
  title: "Model Performance",
  fillColor: GREEN_FILL,
  bottomLabel: "Baseline",
  topLabel: "+89%",
  bottomFontSize: 14,
} as const;
