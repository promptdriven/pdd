import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CHART_LEFT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  AMBER_CURVE_COLOR,
  X_MAX,
  DEBT_EXPONENTIAL_DATA,
  CURVE_DRAW_START,
  CURVE_DRAW_DURATION,
  type DataPoint,
} from './constants';

/** Convert a normalised DataPoint to pixel coordinates */
function toPixel(pt: DataPoint): { px: number; py: number } {
  const px = CHART_LEFT + (pt.x / X_MAX) * CHART_WIDTH;
  // y=0 → CHART_BOTTOM, y=1 → CHART_TOP
  const py = CHART_BOTTOM - pt.y * CHART_HEIGHT;
  return { px, py };
}

/** Build a smooth SVG path through the data using monotone cubic interpolation */
function buildCurvePath(data: DataPoint[]): string {
  if (data.length < 2) return '';
  const pts = data.map(toPixel);

  let d = `M ${pts[0].px} ${pts[0].py}`;
  for (let i = 0; i < pts.length - 1; i++) {
    const p0 = pts[Math.max(0, i - 1)];
    const p1 = pts[i];
    const p2 = pts[i + 1];
    const p3 = pts[Math.min(pts.length - 1, i + 2)];

    const tension = 0.33;
    const cp1x = p1.px + (p2.px - p0.px) * tension;
    const cp1y = p1.py + (p2.py - p0.py) * tension;
    const cp2x = p2.px - (p3.px - p1.px) * tension;
    const cp2y = p2.py - (p3.py - p1.py) * tension;

    d += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${p2.px} ${p2.py}`;
  }
  return d;
}

/** Build a closed path for the shaded area under the curve */
function buildAreaPath(data: DataPoint[]): string {
  const curvePath = buildCurvePath(data);
  const lastPt = toPixel(data[data.length - 1]);
  const firstPt = toPixel(data[0]);
  return `${curvePath} L ${lastPt.px} ${CHART_BOTTOM} L ${firstPt.px} ${CHART_BOTTOM} Z`;
}

export const AnimatedCurve: React.FC = () => {
  const frame = useCurrentFrame();

  // Progress of the curve drawing (easeIn quad for accelerating feel)
  const drawProgress = interpolate(
    frame,
    [CURVE_DRAW_START, CURVE_DRAW_START + CURVE_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.in(Easing.quad) }
  );

  const curvePath = buildCurvePath(DEBT_EXPONENTIAL_DATA);
  const areaPath = buildAreaPath(DEBT_EXPONENTIAL_DATA);

  // We use a very long stroke-dasharray to simulate drawing
  const pathLength = 3000;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Shaded area under the curve */}
      <defs>
        <clipPath id="curve-reveal-clip">
          <rect
            x={CHART_LEFT}
            y={CHART_TOP}
            width={CHART_WIDTH * drawProgress}
            height={CHART_HEIGHT + 10}
          />
        </clipPath>
      </defs>

      <path
        d={areaPath}
        fill={AMBER_CURVE_COLOR}
        fillOpacity={0.08}
        clipPath="url(#curve-reveal-clip)"
      />

      {/* The curve line itself */}
      <path
        d={curvePath}
        fill="none"
        stroke={AMBER_CURVE_COLOR}
        strokeWidth={3}
        strokeLinecap="round"
        strokeDasharray={pathLength}
        strokeDashoffset={pathLength * (1 - drawProgress)}
      />
    </svg>
  );
};
