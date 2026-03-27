// ── Colors ──────────────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const INSET_BG_COLOR = "#0F172A";
export const INSET_BORDER_COLOR = "#334155";
export const LINE_COLOR = "#EF4444";
export const TITLE_COLOR = "#E2E8F0";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const DEGRADATION_LABEL_COLOR = "#EF4444";
export const CYCLE_ANNOTATION_COLOR = "#F59E0B";
export const GRID_CELL_COLOR = "#1E293B";
export const GRID_CELL_HIGHLIGHT = "#334155";
export const DEBT_AREA_COLOR = "#7C3AED";
export const DEBT_AREA_FILL = "rgba(124, 58, 237, 0.15)";

// ── Dimensions ──────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

export const INSET_X = 1350;
export const INSET_Y = 680;
export const INSET_WIDTH = 480;
export const INSET_HEIGHT = 300;
export const INSET_BORDER_RADIUS = 8;
export const INSET_PADDING = 24;

// ── Chart area within the inset (after padding) ─────────────────────────
export const CHART_LEFT = 50;
export const CHART_TOP = 40;
export const CHART_RIGHT = INSET_WIDTH - 30;
export const CHART_BOTTOM = INSET_HEIGHT - 40;
export const CHART_PLOT_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_PLOT_HEIGHT = CHART_BOTTOM - CHART_TOP;

// ── Performance data points ─────────────────────────────────────────────
export interface DataPoint {
  label: string;
  x: number; // 0..1 normalized position on x-axis
  y: number; // 0..1 normalized performance value
}

export const PERFORMANCE_DATA: DataPoint[] = [
  { label: "4K", x: 0, y: 1.0 },
  { label: "32K", x: 0.33, y: 0.86 },
  { label: "128K", x: 0.67, y: 0.5 },
  { label: "1M", x: 1.0, y: 0.15 },
];

// ── Y-axis ticks ────────────────────────────────────────────────────────
export const Y_TICKS = [
  { label: "100%", value: 1.0 },
  { label: "75%", value: 0.75 },
  { label: "50%", value: 0.5 },
  { label: "25%", value: 0.25 },
  { label: "15%", value: 0.15 },
];

// ── Animation frame ranges ─────────────────────────────────────────────
export const TOTAL_FRAMES = 1470;

// Phase 1: Grid dims, inset border draws in
export const PHASE_GRID_DIM_START = 0;
export const PHASE_GRID_DIM_END = 60;

// Phase 2: Inset fills, title types in
export const PHASE_INSET_FILL_START = 60;
export const PHASE_INSET_FILL_END = 90;

// Phase 3: Axes draw, line animates
export const PHASE_LINE_DRAW_START = 90;
export const PHASE_LINE_DRAW_END = 210;

// Phase 4: Labels appear
export const PHASE_LABELS_START = 210;
export const PHASE_LABELS_END = 360;

// Phase 5: Hold
export const PHASE_HOLD_START = 360;
export const PHASE_HOLD_END = 600;

// Phase 6: Inset fades out
export const PHASE_INSET_FADEOUT_START = 600;
export const PHASE_INSET_FADEOUT_END = 720;

// Phase 7: Context rot pulse + annotation
export const PHASE_ROT_PULSE_START = 720;
export const PHASE_ROT_ANNOTATION_START = 810; // 720 + 90
export const PHASE_ROT_END = 900;

// Phase 8: Final hold
export const PHASE_FINAL_HOLD_START = 900;
export const PHASE_FINAL_HOLD_END = 1470;

// ── Grid config ─────────────────────────────────────────────────────────
export const GRID_COLS = 24;
export const GRID_ROWS = 14;
export const GRID_CELL_SIZE = 32;
export const GRID_GAP = 4;

// ── Debt area chart config ──────────────────────────────────────────────
export const DEBT_CHART_LEFT = 160;
export const DEBT_CHART_TOP = 120;
export const DEBT_CHART_WIDTH = 1600;
export const DEBT_CHART_HEIGHT = 700;
