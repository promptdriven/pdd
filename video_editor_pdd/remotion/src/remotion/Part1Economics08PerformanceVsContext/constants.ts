// ─── Colors ───────────────────────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const INSET_BG_COLOR = '#0F172A';
export const INSET_BORDER_COLOR = '#334155';
export const GRID_LINE_COLOR = '#1E293B';
export const TITLE_COLOR = '#E2E8F0';
export const AXIS_LABEL_COLOR = '#94A3B8';
export const LINE_COLOR = '#EF4444';
export const DEGRADATION_LABEL_COLOR = '#EF4444';
export const SOURCE_LABEL_COLOR = '#94A3B8';
export const CYCLE_ANNOTATION_COLOR = '#F59E0B';
export const DEBT_AREA_COLOR = '#F59E0B';

// ─── Canvas ───────────────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// ─── Inset Chart ──────────────────────────────────────────────────────────────
export const INSET_X = 1350;
export const INSET_Y = 680;
export const INSET_WIDTH = 480;
export const INSET_HEIGHT = 300;
export const INSET_BORDER_RADIUS = 8;
export const INSET_PADDING = 40;
export const CHART_PADDING_TOP = 44;
export const CHART_PADDING_BOTTOM = 36;
export const CHART_PADDING_LEFT = 60;
export const CHART_PADDING_RIGHT = 20;

// ─── Performance Data ─────────────────────────────────────────────────────────
export const PERFORMANCE_DATA = [
  { label: '4K', value: 1.0 },
  { label: '32K', value: 0.86 },
  { label: '128K', value: 0.50 },
  { label: '1M', value: 0.15 },
] as const;

// ─── Timing (frames) ─────────────────────────────────────────────────────────
export const TOTAL_FRAMES = 1470;

// Phase 1: Grid dims, inset border draws
export const PHASE_GRID_DIM_START = 0;
export const PHASE_GRID_DIM_END = 60;

// Phase 2: Inset bg fills, title types
export const PHASE_INSET_BG_START = 60;
export const PHASE_INSET_BG_END = 90;

// Phase 3: Axes draw, line animates
export const PHASE_AXES_START = 90;
export const PHASE_LINE_DRAW_START = 90;
export const PHASE_LINE_DRAW_END = 210;

// Phase 4: Labels appear
export const PHASE_LABELS_START = 210;
export const PHASE_LABELS_FADE_DURATION = 20;

// Phase 5: Hold on inset
export const PHASE_INSET_HOLD_END = 600;

// Phase 6: Inset fades out
export const PHASE_INSET_FADE_START = 600;
export const PHASE_INSET_FADE_END = 720;

// Phase 7: Context rot pulse + annotation
export const PHASE_PULSE_START = 720;
export const PHASE_ANNOTATION_START = 810; // 720 + 90
export const PHASE_ANNOTATION_FADE_DURATION = 20;
export const PULSE_CYCLE_FRAMES = 45;

// ─── Grid Background ─────────────────────────────────────────────────────────
export const GRID_CELL_SIZE = 32;
export const GRID_COLS = Math.ceil(CANVAS_WIDTH / GRID_CELL_SIZE);
export const GRID_ROWS = Math.ceil(CANVAS_HEIGHT / GRID_CELL_SIZE);

// ─── Debt Area Chart (simplified stand-in) ────────────────────────────────────
export const DEBT_CHART_LEFT = 160;
export const DEBT_CHART_TOP = 160;
export const DEBT_CHART_WIDTH = 1600;
export const DEBT_CHART_HEIGHT = 700;
