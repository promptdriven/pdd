// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";
export const DURATION_FRAMES = 1170;
export const FPS = 30;

// Chart area (matches spec 03 layout)
export const CHART_LEFT = 140;
export const CHART_TOP = 100;
export const CHART_WIDTH = 1200;
export const CHART_HEIGHT = 600;
export const CHART_RIGHT = CHART_LEFT + CHART_WIDTH;
export const CHART_BOTTOM = CHART_TOP + CHART_HEIGHT;

// Chart data range
export const YEAR_MIN = 2020;
export const YEAR_MAX = 2026;
export const COST_MIN = 0;
export const COST_MAX = 100;

// Chart axis colors
export const AXIS_COLOR = "#334155";
export const AXIS_LABEL_COLOR = "#64748B";
export const GRID_COLOR = "#1E293B";

// Line colors
export const AMBER_LINE_COLOR = "#F59E0B";
export const AMBER_DASHED_COLOR = "#F59E0B";

// Annotation callout styles
export const CALLOUT_FILL = "#1E293B";
export const CALLOUT_RADIUS = 8;
export const CALLOUT_BORDER_WIDTH = 1.5;

// Annotation 1 — GitHub Study
export const GITHUB_ACCENT = "#4A90D9";
export const GITHUB_MAIN_TEXT = "Individual task: \u221255%";
export const GITHUB_SOURCE = "(GitHub, 2022)";
export const GITHUB_FINE_PRINT = "95 developers, one greenfield task";
export const GITHUB_CALLOUT_X = 1400;
export const GITHUB_CALLOUT_Y = 520;
export const GITHUB_TARGET_YEAR = 2023;

// Annotation 2 — Uplevel Study
export const UPLEVEL_ACCENT = "#EF4444";
export const UPLEVEL_MAIN_TEXT = "Overall throughput: ~0%";
export const UPLEVEL_SOURCE = "(Uplevel, 2024)";
export const UPLEVEL_FINE_PRINT = "785 developers, one year";
export const UPLEVEL_CALLOUT_X = 1400;
export const UPLEVEL_CALLOUT_Y = 220;
export const UPLEVEL_TARGET_YEAR = 2024;

// Connector line target points on chart (pixel coords for connector endpoints)
// GitHub connector: points to the solid amber line near year 2023
export const GITHUB_CONNECTOR_TARGET_X = CHART_LEFT + ((2023 - YEAR_MIN) / (YEAR_MAX - YEAR_MIN)) * CHART_WIDTH;
export const GITHUB_CONNECTOR_TARGET_Y = 490; // on the dropping solid amber line

// Uplevel connector: points to the dashed amber line near year 2024
export const UPLEVEL_CONNECTOR_TARGET_X = CHART_LEFT + ((2024 - YEAR_MIN) / (YEAR_MAX - YEAR_MIN)) * CHART_WIDTH;
export const UPLEVEL_CONNECTOR_TARGET_Y = 260; // on the nearly-flat dashed amber line

// Contrast line between annotation boxes
export const CONTRAST_LINE_COLOR = "#FFFFFF";
export const CONTRAST_LINE_OPACITY = 0.08;

// Typography
export const FONT_FAMILY = "Inter, sans-serif";
export const MAIN_TEXT_SIZE = 18;
export const SOURCE_TEXT_SIZE = 14;
export const FINE_PRINT_SIZE = 12;
export const SOURCE_COLOR = "#94A3B8";
export const FINE_PRINT_COLOR = "#64748B";
export const FINE_PRINT_OPACITY = 0.7;

// Animation timing (frames)
export const ANNOTATION1_START = 60;
export const ANNOTATION1_CONNECTOR_DRAW = 30;
export const ANNOTATION1_BOX_SCALE = 20;
export const ANNOTATION1_HOLD_END = 300;

export const ANNOTATION2_START = 300;
export const ANNOTATION2_CONNECTOR_DRAW = 30;
export const ANNOTATION2_BOX_SCALE = 20;

export const CONTRAST_LINE_START = 390;
export const CONTRAST_LINE_DRAW = 30;

// Solid amber line data points (immediate patch cost — drops)
export const SOLID_LINE_POINTS: { x: number; y: number }[] = [
  { x: 2020, y: 80 },
  { x: 2021, y: 75 },
  { x: 2022, y: 60 },
  { x: 2023, y: 36 },
  { x: 2024, y: 28 },
  { x: 2025, y: 22 },
  { x: 2026, y: 18 },
];

// Dashed amber line data points (total cost with debt — stays flat/rises)
export const DASHED_LINE_POINTS: { x: number; y: number }[] = [
  { x: 2020, y: 80 },
  { x: 2021, y: 78 },
  { x: 2022, y: 77 },
  { x: 2023, y: 78 },
  { x: 2024, y: 80 },
  { x: 2025, y: 82 },
  { x: 2026, y: 84 },
];

// Chart y-axis labels
export const Y_AXIS_LABELS = ["0%", "25%", "50%", "75%", "100%"];
