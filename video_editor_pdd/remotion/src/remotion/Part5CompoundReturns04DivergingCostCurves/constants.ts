// === Colors ===
export const COLORS = {
  background: '#0F172A',
  gridLine: '#1E293B',
  axis: '#475569',
  axisLabel: '#64748B',
  patching: '#D9944A',
  pdd: '#4A90D9',
  text: '#E2E8F0',
  pillBg: '#1E293B',
} as const;

// === Dimensions ===
export const CHART = {
  originX: 180,
  originY: 780,
  xAxisY: 820,
  yAxisX: 180,
  endX: 1700,
  width: 1920,
  height: 1080,
  gridHSpacing: 80,
} as const;

// === Curve Data (pixel coordinates) ===
// Patching: exponential rise
export const PATCHING_POINTS: [number, number][] = [
  [180, 780],
  [332, 755],   // Year 1
  [484, 720],   // Year 2
  [636, 670],   // Year 3
  [788, 590],   // Year 4
  [940, 480],   // Year 5
  [1092, 360],  // Year 6
  [1244, 260],  // Year 7
  [1396, 180],  // Year 8
  [1548, 120],  // Year 9
  [1700, 80],   // Year 10
];

// PDD: flat/gentle decline
export const PDD_POINTS: [number, number][] = [
  [180, 780],
  [332, 770],   // Year 1
  [484, 762],   // Year 2
  [636, 756],   // Year 3
  [788, 750],   // Year 4
  [940, 745],   // Year 5
  [1092, 740],  // Year 6
  [1244, 735],  // Year 7
  [1396, 730],  // Year 8
  [1548, 725],  // Year 9
  [1700, 720],  // Year 10
];

// X-axis labels
export const X_LABELS = [
  { text: 'Year 0', x: 180 },
  { text: 'Year 2', x: 484 },
  { text: 'Year 4', x: 788 },
  { text: 'Year 6', x: 1092 },
  { text: 'Year 8', x: 1396 },
  { text: 'Year 10', x: 1700 },
];

// === Animation Timing (frames) ===
export const TIMING = {
  axesStart: 0,
  axesDuration: 30,
  curvesStart: 30,
  curvesDuration: 150,
  gapFillStart: 180,
  gapFillDuration: 60,
  annotationsStart: 240,
  annotationsDuration: 25,
  gapLabelStart: 300,
  gapLabelDuration: 20,
  totalDuration: 420,
} as const;

// Helper: interpolate Y on a curve at a given X
export function interpolateY(points: [number, number][], x: number): number {
  for (let i = 0; i < points.length - 1; i++) {
    const [x0, y0] = points[i];
    const [x1, y1] = points[i + 1];
    if (x >= x0 && x <= x1) {
      const t = (x - x0) / (x1 - x0);
      return y0 + t * (y1 - y0);
    }
  }
  return points[points.length - 1][1];
}

// Convert points array to SVG path string
export function pointsToPath(points: [number, number][]): string {
  if (points.length === 0) return '';
  const [startX, startY] = points[0];
  let d = `M ${startX} ${startY}`;

  // Use cubic bezier for smooth curves
  for (let i = 1; i < points.length; i++) {
    const [prevX, prevY] = points[i - 1];
    const [currX, currY] = points[i];
    const cpX = (prevX + currX) / 2;
    d += ` C ${cpX} ${prevY}, ${cpX} ${currY}, ${currX} ${currY}`;
  }
  return d;
}
