// Colors
export const BG_COLOR = '#0A0F1A';
export const AXIS_COLOR = '#334155';
export const AXIS_LABEL_COLOR = '#64748B';
export const TITLE_COLOR = '#E2E8F0';
export const CURVE_COLOR = '#4A90D9';
export const LEFT_ZONE_COLOR = '#D9944A';
export const RIGHT_ZONE_COLOR = '#5AAA6E';
export const SLIDER_COLOR = '#E2E8F0';

// Dimensions
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Chart area
export const CHART_LEFT = 260;
export const CHART_RIGHT = 1620;
export const CHART_TOP = 180;
export const CHART_BOTTOM = 820;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT; // 1360
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP; // 640

// X-axis ticks
export const X_TICKS = [0, 10, 20, 30, 40, 50];
export const Y_TICK_LABELS = ['Low', 'Medium', 'High'];

// Curve function: maps x (0-50 test count) to pixel y
export function curveY(testCount: number): number {
  return CHART_TOP + (CHART_HEIGHT) * (1 / (1 + 0.08 * testCount));
}

// Map test count to pixel x
export function curveX(testCount: number): number {
  return CHART_LEFT + (testCount / 50) * CHART_WIDTH;
}

// Generate curve points for SVG path
export function generateCurvePoints(steps: number = 200): Array<[number, number]> {
  const points: Array<[number, number]> = [];
  for (let i = 0; i <= steps; i++) {
    const t = i / steps;
    const testCount = t * 50;
    points.push([curveX(testCount), curveY(testCount)]);
  }
  return points;
}

// Build SVG path string from points
export function buildCurvePath(points: Array<[number, number]>): string {
  if (points.length === 0) return '';
  let d = `M ${points[0][0]} ${points[0][1]}`;
  for (let i = 1; i < points.length; i++) {
    d += ` L ${points[i][0]} ${points[i][1]}`;
  }
  return d;
}

// Animation frame ranges
export const ANIM = {
  AXES_START: 0,
  AXES_END: 30,
  TICKS_START: 30,
  TICKS_END: 60,
  CURVE_START: 60,
  CURVE_END: 180,
  LEFT_ZONE_START: 180,
  LEFT_ZONE_END: 240,
  RIGHT_ZONE_START: 240,
  RIGHT_ZONE_END: 300,
  SLIDER_START: 300,
  SLIDER_END: 390,
  HOLD_START: 390,
  HOLD_END: 450,
} as const;

export const TOTAL_FRAMES = 450;
export const FPS = 30;
