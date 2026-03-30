// ── Canvas ──────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 1170;
export const FPS = 30;

// ── Background ─────────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';

// ── Chart region (the underlying cost chart that this overlay sits on) ──
export const CHART_LEFT = 160;
export const CHART_RIGHT = 1760;
export const CHART_TOP = 140;
export const CHART_BOTTOM = 860;
export const CHART_YEAR_START = 2019;
export const CHART_YEAR_END = 2026;

// ── Accent colours ─────────────────────────────────────────────────
export const BLUE_ACCENT = '#4A90D9';
export const RED_ACCENT = '#EF4444';
export const AMBER_LINE_COLOR = '#F59E0B';
export const AMBER_DASHED_COLOR = '#F59E0B';

// ── Callout box ────────────────────────────────────────────────────
export const CALLOUT_FILL = '#1E293B';
export const CALLOUT_BORDER_WIDTH = 1.5;
export const CALLOUT_BORDER_RADIUS = 8;
export const CALLOUT_PADDING = 16;
export const CALLOUT_WIDTH = 340;

// ── Typography colours ─────────────────────────────────────────────
export const TEXT_SOURCE_COLOR = '#94A3B8';
export const TEXT_FINEPRINT_COLOR = '#64748B';
export const TEXT_FINEPRINT_OPACITY = 0.78; // raised from 0.7 to meet overlay minimum

// ── Contrast connector ─────────────────────────────────────────────
export const CONTRAST_LINE_COLOR = '#FFFFFF';
export const CONTRAST_LINE_OPACITY = 0.08;

// ── Grid / axis colours ────────────────────────────────────────────
export const GRID_LINE_COLOR = '#1E293B';
export const AXIS_LABEL_COLOR = '#64748B';

// ── Animation frame ranges ─────────────────────────────────────────
export const ANNOTATION1_START = 60;
export const ANNOTATION1_CONNECTOR_DURATION = 30;
export const ANNOTATION1_BOX_DURATION = 20;
export const ANNOTATION1_TEXT_RATE = 2; // frames per character

export const ANNOTATION2_START = 300;
export const ANNOTATION2_CONNECTOR_DURATION = 30;
export const ANNOTATION2_BOX_DURATION = 20;
export const ANNOTATION2_TEXT_RATE = 2;

export const CONTRAST_LINE_START = 390;
export const CONTRAST_LINE_DURATION = 30;

// ── Annotation positions (px) ──────────────────────────────────────
export const ANNOTATION1_BOX_X = 1340;
export const ANNOTATION1_BOX_Y = 480;
export const ANNOTATION1_TARGET_X = 1160; // where the solid amber line is near 2023
export const ANNOTATION1_TARGET_Y = 640;

export const ANNOTATION2_BOX_X = 1340;
export const ANNOTATION2_BOX_Y = 180;
export const ANNOTATION2_TARGET_X = 1320; // where the dashed amber line is near 2024
export const ANNOTATION2_TARGET_Y = 310;

// ── Chart data for the underlying cost chart ───────────────────────
// Solid amber line: "immediate patch cost" – drops steeply
export const SOLID_LINE_POINTS: [number, number][] = [
  [2019, 0.95],
  [2020, 0.90],
  [2021, 0.80],
  [2022, 0.65],
  [2023, 0.40],
  [2024, 0.28],
  [2025, 0.20],
  [2026, 0.15],
];

// Dashed amber line: "total cost with debt" – stays nearly flat
export const DASHED_LINE_POINTS: [number, number][] = [
  [2019, 0.95],
  [2020, 0.93],
  [2021, 0.92],
  [2022, 0.90],
  [2023, 0.88],
  [2024, 0.87],
  [2025, 0.86],
  [2026, 0.85],
];
