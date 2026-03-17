// Colors
export const BG_COLOR = '#0F172A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.06;
export const AXIS_COLOR = '#475569';
export const AXIS_OPACITY = 0.5;
export const LABEL_COLOR = '#64748B';
export const LABEL_OPACITY = 0.4;

export const DEBT_CURVE_COLOR = '#D9944A';
export const REGEN_COLOR = '#4A90D9';

export const CALLOUT_BG = '#1E293B';
export const CALLOUT_NUMBER_COLOR = '#E2E8F0';
export const CALLOUT_SUBTITLE_COLOR = '#94A3B8';
export const CALLOUT_SOURCE_COLOR = '#64748B';

// Dimensions
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Chart area
export const CHART_LEFT = 200;
export const CHART_RIGHT = 1700;
export const CHART_TOP = 200;
export const CHART_BOTTOM = 800;

// Grid
export const H_GRID_SPACING = 100;
export const V_GRID_SPACING = 150;

// Axis labels
export const X_LABELS = ['Year 1', 'Year 3', 'Year 5', 'Year 7', 'Year 10'];
export const Y_LABELS = ['$', '$$', '$$$', '$$$$'];

// Exponential debt curve data points (x in chart coords)
// Maps from data: x=1..10, y=1..24 to chart pixels
export const DEBT_DATA_POINTS: { x: number; y: number }[] = [
  { x: 1, y: 1.0 },
  { x: 2, y: 1.4 },
  { x: 3, y: 2.1 },
  { x: 5, y: 4.2 },
  { x: 7, y: 8.5 },
  { x: 10, y: 24.0 },
];

// Map data to pixel coords
export function dataToPixel(
  dataX: number,
  dataY: number,
): { x: number; y: number } {
  const xRange = 10 - 1; // data x range
  const yRange = 24 - 0; // data y range
  const px = CHART_LEFT + ((dataX - 1) / xRange) * (CHART_RIGHT - CHART_LEFT);
  const py = CHART_BOTTOM - (dataY / yRange) * (CHART_BOTTOM - CHART_TOP);
  return { x: px, y: py };
}

// Build the full exponential curve as pixel points (many intermediate points for smooth curve)
export function buildExponentialCurvePixels(numPoints = 200): { x: number; y: number }[] {
  const points: { x: number; y: number }[] = [];
  for (let i = 0; i <= numPoints; i++) {
    const t = i / numPoints;
    const dataX = 1 + t * 9; // 1..10
    // Exponential: y = 1 * (1 + 0.38)^(x-1), fitted to reach ~24 at x=10
    const dataY = Math.pow(1.38, dataX - 1);
    points.push(dataToPixel(dataX, Math.min(dataY, 24)));
  }
  return points;
}

// Sawtooth line config
export const SAWTOOTH_BASELINE_Y = 720; // pixel y for baseline
export const SAWTOOTH_PEAK_Y = 650; // pixel y for peak (lower value = higher on screen)
export const SAWTOOTH_TEETH = 5;
export const SAWTOOTH_START_X = CHART_LEFT;
export const SAWTOOTH_END_X = CHART_RIGHT;

// Build sawtooth points
export function buildSawtoothPixels(): { x: number; y: number }[] {
  const points: { x: number; y: number }[] = [];
  const totalWidth = SAWTOOTH_END_X - SAWTOOTH_START_X;
  const toothWidth = totalWidth / SAWTOOTH_TEETH;

  for (let i = 0; i < SAWTOOTH_TEETH; i++) {
    const toothStartX = SAWTOOTH_START_X + i * toothWidth;
    // Flat segment (most of the tooth width)
    points.push({ x: toothStartX, y: SAWTOOTH_BASELINE_Y });
    // Rise to peak (at ~80% of tooth width, over 30px equivalent)
    const riseX = toothStartX + toothWidth * 0.8;
    points.push({ x: riseX, y: SAWTOOTH_BASELINE_Y });
    points.push({ x: riseX + 30, y: SAWTOOTH_PEAK_Y });
    // Fall back down (over 10px)
    points.push({ x: riseX + 40, y: SAWTOOTH_BASELINE_Y });
  }
  // Final flat segment to the end
  points.push({ x: SAWTOOTH_END_X, y: SAWTOOTH_BASELINE_Y });

  return points;
}

// Animation timing (frames)
export const FPS = 30;
export const TOTAL_FRAMES = 360;

export const AXES_DRAW_START = 0;
export const AXES_DRAW_DURATION = 20;
export const GRID_FADE_DURATION = 30;

export const CURVE_DRAW_START = 30;
export const CURVE_DRAW_DURATION = 120;
export const FORMULA_APPEAR_FRAME = 120;

export const SAWTOOTH_DRAW_START = 90;
export const SAWTOOTH_DRAW_DURATION = 120;

export const GAP_FILL_START = 210;
export const GAP_FILL_DURATION = 30;

export const CALLOUT_FADE_START = 210;
export const CALLOUT_FADE_DURATION = 20;

export const NUMBER_SCALE_START = 270;
export const NUMBER_SCALE_DURATION = 15;
