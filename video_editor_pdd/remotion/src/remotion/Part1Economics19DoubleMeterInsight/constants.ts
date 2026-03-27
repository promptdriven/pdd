// === Colors ===
export const BG_COLOR_START = "#050810";
export const BG_COLOR_END = "#0A0F1A";

export const TRACK_FILL_COLOR = "#1E293B";
export const TRACK_BORDER_COLOR = "#334155";

export const CONTEXT_FILL_COLOR = "#4A90D9";
export const PERFORMANCE_FILL_COLOR = "#5AAA6E";

export const LABEL_DIM_COLOR = "#64748B";
export const TEXT_PRIMARY_COLOR = "#E2E8F0";
export const ACCENT_AND_COLOR = "#F59E0B";

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

export const METER_WIDTH = 80;
export const METER_HEIGHT = 600;
export const METER_BORDER_RADIUS = 8;
export const METER_BORDER_WIDTH = 1;

export const LEFT_METER_X = 560;
export const RIGHT_METER_X = 1360;
export const METER_Y = 200;

export const INSIGHT_TEXT_Y = 900;

// === Animation Frames ===
export const TOTAL_FRAMES = 360;

// Phase 1: Background lighten + meter tracks draw (0-30)
export const BG_LIGHTEN_START = 0;
export const BG_LIGHTEN_END = 30;

// Phase 2: Titles + bottom labels appear (30-60)
export const LABELS_APPEAR_START = 30;
export const LABELS_APPEAR_END = 60;

// Phase 3: Meters fill (60-180)
export const FILL_START = 60;
export const FILL_END = 180;
export const FILL_DURATION = 120;

// Phase 4: Top labels appear (180-210)
export const TOP_LABELS_START = 180;
export const TOP_LABELS_END = 210;

// Phase 5: Pulse effect (210-270)
export const PULSE_START = 210;
export const PULSE_END = 270;
export const PULSE_CYCLE = 30;

// Phase 6: Insight text (270-330)
export const INSIGHT_TEXT_START = 270;
export const INSIGHT_TEXT_FADE_DURATION = 30;

// === Typography ===
export const FONT_FAMILY = "Inter, sans-serif";
