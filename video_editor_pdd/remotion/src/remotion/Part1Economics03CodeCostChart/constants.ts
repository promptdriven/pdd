// ─── Colors ───
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.08;
export const AXIS_COLOR = '#334155';
export const LABEL_COLOR = '#94A3B8';
export const BLUE_LINE_COLOR = '#4A90D9';
export const AMBER_LINE_COLOR = '#D9944A';
export const DEBT_FILL_OPACITY = 0.12;
export const MARKER_LINE_COLOR = '#64748B';

// ─── Layout ───
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const CHART_LEFT = 140;
export const CHART_RIGHT = 1800;
export const CHART_TOP = 100;
export const CHART_BOTTOM = 920;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// ─── Data range ───
export const X_MIN = 2000;
export const X_MAX = 2026;
export const Y_MIN = 0;
export const Y_MAX = 1.0;

// ─── Timing (frames) ───
export const TOTAL_FRAMES = 1650;
export const AXES_DRAW_START = 0;
export const AXES_DRAW_END = 45;
export const BLUE_LINE_START = 45;
export const BLUE_LINE_END = 300;
export const AMBER_SOLID_START = 300;
export const AMBER_SOLID_END = 450;
export const PULSE_START = 450;
export const PULSE_END = 540;
export const DASHED_LINE_START = 540;
export const DASHED_LINE_END = 600;
export const PULLBACK_START = 600;
export const PULLBACK_END = 690;

// ─── Series data ───
export interface DataPoint {
  x: number;
  y: number;
}

export const GENERATE_COST_DATA: DataPoint[] = [
  { x: 2000, y: 0.9 },
  { x: 2010, y: 0.88 },
  { x: 2020, y: 0.85 },
  { x: 2021, y: 0.82 },
  { x: 2022, y: 0.78 },
  { x: 2023, y: 0.65 },
  { x: 2024, y: 0.35 },
  { x: 2025, y: 0.18 },
  { x: 2026, y: 0.1 },
];

export const IMMEDIATE_PATCH_DATA: DataPoint[] = [
  { x: 2000, y: 0.55 },
  { x: 2010, y: 0.52 },
  { x: 2020, y: 0.48 },
  { x: 2021, y: 0.42 },
  { x: 2022, y: 0.35 },
  { x: 2023, y: 0.28 },
  { x: 2024, y: 0.22 },
  { x: 2025, y: 0.18 },
  { x: 2026, y: 0.15 },
];

export const TOTAL_COST_DEBT_DATA: DataPoint[] = [
  { x: 2000, y: 0.6 },
  { x: 2010, y: 0.62 },
  { x: 2020, y: 0.65 },
  { x: 2021, y: 0.66 },
  { x: 2022, y: 0.68 },
  { x: 2023, y: 0.7 },
  { x: 2024, y: 0.72 },
  { x: 2025, y: 0.73 },
  { x: 2026, y: 0.74 },
];

// ─── Date markers ───
export interface DateMarkerDef {
  year: number;
  label: string;
}

export const DATE_MARKERS: DateMarkerDef[] = [
  { year: 2021, label: 'Codex' },
  { year: 2023, label: 'GPT-4' },
  { year: 2023.5, label: 'Claude' },
  { year: 2024, label: 'Gemini' },
];

// ─── Legend entries ───
export interface LegendEntry {
  label: string;
  color: string;
  dashed: boolean;
}

export const LEGEND_ITEMS: LegendEntry[] = [
  { label: 'Cost to generate', color: BLUE_LINE_COLOR, dashed: false },
  { label: 'Immediate patch cost', color: AMBER_LINE_COLOR, dashed: false },
  { label: 'Total cost (with debt)', color: AMBER_LINE_COLOR, dashed: true },
];

// ─── Coordinate helpers ───
export function dataToPixelX(xVal: number): number {
  return CHART_LEFT + ((xVal - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
}

export function dataToPixelY(yVal: number): number {
  return CHART_BOTTOM - ((yVal - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;
}

export function dataToSvgPath(data: DataPoint[]): string {
  return data
    .map((pt, i) => {
      const px = dataToPixelX(pt.x);
      const py = dataToPixelY(pt.y);
      return `${i === 0 ? 'M' : 'L'} ${px} ${py}`;
    })
    .join(' ');
}

/** Get total path length by summing segment distances */
export function getPathLength(data: DataPoint[]): number {
  let total = 0;
  for (let i = 1; i < data.length; i++) {
    const x0 = dataToPixelX(data[i - 1].x);
    const y0 = dataToPixelY(data[i - 1].y);
    const x1 = dataToPixelX(data[i].x);
    const y1 = dataToPixelY(data[i].y);
    total += Math.sqrt((x1 - x0) ** 2 + (y1 - y0) ** 2);
  }
  return total;
}
