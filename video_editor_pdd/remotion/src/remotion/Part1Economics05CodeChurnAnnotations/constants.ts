// === Colors ===
export const BG_COLOR = '#0A0F1A';
export const CALLOUT_BG = '#1E293B';
export const CHURN_ACCENT = '#EF4444';
export const REFACTOR_ACCENT = '#F59E0B';
export const SOURCE_TEXT_COLOR = '#94A3B8';
export const LABEL_TEXT_COLOR_WHITE = '#FFFFFF';

// === Chart colors (underlying chart that annotations overlay) ===
export const CHART_GRID_COLOR = 'rgba(148, 163, 184, 0.12)';
export const CHART_SOLID_LINE = '#F59E0B';
export const CHART_DASHED_LINE = '#3B82F6';
export const DEBT_AREA_COLOR = 'rgba(239, 68, 68, 0.15)';

// === Dimensions ===
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const TOTAL_FRAMES = 840;
export const FPS = 30;

// === Chart layout ===
export const CHART_LEFT = 140;
export const CHART_RIGHT = 1300;
export const CHART_TOP = 180;
export const CHART_BOTTOM = 820;

// === Annotation positions ===
export const ANNOTATION_1_X = 1380;
export const ANNOTATION_1_Y = 340;
export const ANNOTATION_2_X = 1380;
export const ANNOTATION_2_Y = 500;

export const CALLOUT_WIDTH = 420;
export const CALLOUT_HEIGHT_MAIN = 80;
export const CALLOUT_BORDER_RADIUS = 8;
export const CALLOUT_BORDER_WIDTH = 1.5;

// === Typography ===
export const FONT_MAIN_SIZE = 18;
export const FONT_SOURCE_SIZE = 12;
export const FONT_FAMILY = 'Inter, sans-serif';

// === Animation timing ===
export const PREV_FADE_START = 0;
export const PREV_FADE_END = 30;
export const PULSE_START = 60;
export const ANNOTATION_1_START = 60;
export const ANNOTATION_2_START = 360;
export const CONNECTOR_DRAW_FRAMES = 30;
export const CALLOUT_SCALE_FRAMES = 20;
export const PULSE_CYCLE_FRAMES = 45;
export const PULSE_MIN_OPACITY = 0.12;
export const PULSE_MAX_OPACITY = 0.20;

// === Chart data points (years on x-axis) ===
export const CHART_YEARS = [2020, 2021, 2022, 2023, 2024, 2025];

// Solid line: total code output (rising)
export const SOLID_LINE_Y = [700, 680, 640, 560, 440, 340];
// Dashed line: maintained/patched code (flatter)
export const DASHED_LINE_Y = [710, 700, 680, 680, 700, 720];

// === Previous annotations (GitHub/Uplevel) that fade out ===
export const PREV_ANNOTATION_1 = {
  text: 'GitHub survey: 55% faster',
  source: '(GitHub, 2024)',
  x: 900,
  y: 260,
  accentColor: '#3B82F6',
};

export const PREV_ANNOTATION_2 = {
  text: 'Uplevel: +41% PRs merged',
  source: '(Uplevel, 2024)',
  x: 900,
  y: 360,
  accentColor: '#8B5CF6',
};
