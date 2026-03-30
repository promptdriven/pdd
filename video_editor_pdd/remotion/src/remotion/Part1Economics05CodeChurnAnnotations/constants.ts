// ─── Background & Canvas ───────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = '#0A0F1A';

// ─── Palette ───────────────────────────────────────────────────────
export const COLOR_RED = '#EF4444';
export const COLOR_AMBER = '#F59E0B';
export const COLOR_SLATE = '#94A3B8';
export const COLOR_SLATE_DARK = '#1E293B';
export const COLOR_WHITE = '#FFFFFF';
export const COLOR_LINE_SOLID = '#3B82F6';
export const COLOR_LINE_DASHED = '#F59E0B';
export const COLOR_DEBT_FILL = '#F59E0B';
export const COLOR_PREV_ANNOTATION_BORDER = '#6366F1';

// ─── Chart Layout ──────────────────────────────────────────────────
export const CHART_LEFT = 120;
export const CHART_RIGHT = 1300;
export const CHART_TOP = 160;
export const CHART_BOTTOM = 820;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// Year labels along x-axis
export const CHART_YEARS = [2020, 2021, 2022, 2023, 2024, 2025] as const;

// ─── Annotation Positions ──────────────────────────────────────────
export const ANNOTATION1_X = 1400;
export const ANNOTATION1_Y = 340;
export const ANNOTATION1_CONNECTOR_TARGET_X = 1100;
export const ANNOTATION1_CONNECTOR_TARGET_Y = 500;

export const ANNOTATION2_X = 1400;
export const ANNOTATION2_Y = 510;
export const ANNOTATION2_CONNECTOR_TARGET_X = 1100;
export const ANNOTATION2_CONNECTOR_TARGET_Y = 640;

export const CALLOUT_WIDTH = 380;
export const CALLOUT_HEIGHT_SINGLE = 70;
export const CALLOUT_BORDER_RADIUS = 8;
export const CALLOUT_BORDER_WIDTH = 1.5;

// ─── Previous Annotations (faded) ─────────────────────────────────
export const PREV_ANNOTATION_1_X = 1400;
export const PREV_ANNOTATION_1_Y = 220;
export const PREV_ANNOTATION_2_X = 1400;
export const PREV_ANNOTATION_2_Y = 340;

// ─── Animation Timing (frames) ─────────────────────────────────────
export const TOTAL_FRAMES = 840;
export const FPS = 30;

// Phase 1: Fade previous annotations (0-60)
export const PREV_FADE_START = 0;
export const PREV_FADE_DURATION = 30;

// Phase 2: Debt pulse + Annotation 1 (60-150)
export const PULSE_START = 60;
export const ANNOTATION1_START = 60;
export const CONNECTOR_DRAW_DURATION = 30;
export const CALLOUT_SCALE_DURATION = 20;
export const TEXT_TYPE_DURATION = 30;

// Phase 3: Hold (150-360)

// Phase 4: Annotation 2 (360-450)
export const ANNOTATION2_START = 360;

// Phase 5: Both visible + pulse (450-840)

// ─── Debt Pulse ────────────────────────────────────────────────────
export const PULSE_MIN_OPACITY = 0.12;
export const PULSE_MAX_OPACITY = 0.20;
export const PULSE_CYCLE_FRAMES = 45;

// ─── Typography ────────────────────────────────────────────────────
export const FONT_MAIN_SIZE = 18;
export const FONT_MAIN_WEIGHT = 700;
export const FONT_SOURCE_SIZE = 12;
export const FONT_SOURCE_WEIGHT = 400;
export const FONT_FAMILY = 'Inter, system-ui, sans-serif';
export const FONT_AXIS_SIZE = 13;
export const FONT_TITLE_SIZE = 22;
