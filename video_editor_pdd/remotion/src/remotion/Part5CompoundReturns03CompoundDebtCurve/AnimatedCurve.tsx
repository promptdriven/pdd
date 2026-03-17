import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  DEBT_CURVE_COLOR,
  CURVE_DRAW_START,
  CURVE_DRAW_DURATION,
  FORMULA_APPEAR_FRAME,
  buildExponentialCurvePixels,
} from './constants';

// Build the SVG path string from points
function pointsToPath(points: { x: number; y: number }[]): string {
  if (points.length === 0) return '';
  let d = `M ${points[0].x} ${points[0].y}`;
  for (let i = 1; i < points.length; i++) {
    d += ` L ${points[i].x} ${points[i].y}`;
  }
  return d;
}

// Compute total path length from points
function computePathLength(points: { x: number; y: number }[]): number {
  let total = 0;
  for (let i = 1; i < points.length; i++) {
    const dx = points[i].x - points[i - 1].x;
    const dy = points[i].y - points[i - 1].y;
    total += Math.sqrt(dx * dx + dy * dy);
  }
  return total;
}

// Get position at a fraction of the path
function getPointAtFraction(
  points: { x: number; y: number }[],
  fraction: number,
): { x: number; y: number } {
  const totalLen = computePathLength(points);
  const targetLen = fraction * totalLen;
  let accumulated = 0;

  for (let i = 1; i < points.length; i++) {
    const dx = points[i].x - points[i - 1].x;
    const dy = points[i].y - points[i - 1].y;
    const segLen = Math.sqrt(dx * dx + dy * dy);
    if (accumulated + segLen >= targetLen) {
      const t = (targetLen - accumulated) / segLen;
      return {
        x: points[i - 1].x + dx * t,
        y: points[i - 1].y + dy * t,
      };
    }
    accumulated += segLen;
  }

  return points[points.length - 1];
}

export const AnimatedCurve: React.FC = () => {
  const frame = useCurrentFrame();
  const curvePoints = useMemo(() => buildExponentialCurvePixels(300), []);
  const pathD = useMemo(() => pointsToPath(curvePoints), [curvePoints]);
  const totalLength = useMemo(() => computePathLength(curvePoints), [curvePoints]);

  // Draw progress with easeIn(cubic) — starts slow, accelerates (matches the math)
  const drawProgress = interpolate(
    frame,
    [CURVE_DRAW_START, CURVE_DRAW_START + CURVE_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.cubic),
    },
  );

  const visibleLength = drawProgress * totalLength;
  const hiddenLength = totalLength - visibleLength;

  // Glow dot position (at the drawing tip)
  const tipPoint = useMemo(
    () => getPointAtFraction(curvePoints, Math.min(drawProgress, 1)),
    [curvePoints, drawProgress],
  );

  // Formula label animation
  const formulaOpacity = interpolate(
    frame,
    [FORMULA_APPEAR_FRAME, FORMULA_APPEAR_FRAME + 30],
    [0, 0.6],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Formula typewriter effect
  const formulaText = 'Debt × (1 + Rate)^Time';
  const formulaCharsVisible = Math.floor(
    interpolate(
      frame,
      [FORMULA_APPEAR_FRAME, FORMULA_APPEAR_FRAME + 40],
      [0, formulaText.length],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      },
    ),
  );

  if (drawProgress <= 0) return null;

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id="curveGlow">
          <feGaussianBlur stdDeviation="6" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Glow trail behind the curve */}
      <path
        d={pathD}
        fill="none"
        stroke={DEBT_CURVE_COLOR}
        strokeWidth={6}
        opacity={0.08}
        strokeDasharray={totalLength}
        strokeDashoffset={hiddenLength}
        filter="url(#curveGlow)"
      />

      {/* Main exponential curve */}
      <path
        d={pathD}
        fill="none"
        stroke={DEBT_CURVE_COLOR}
        strokeWidth={3}
        strokeDasharray={totalLength}
        strokeDashoffset={hiddenLength}
        strokeLinecap="round"
      />

      {/* Glowing tip dot */}
      {drawProgress > 0 && drawProgress < 1 && (
        <circle
          cx={tipPoint.x}
          cy={tipPoint.y}
          r={5}
          fill={DEBT_CURVE_COLOR}
          opacity={0.6}
          filter="url(#curveGlow)"
        />
      )}

      {/* Formula label */}
      {formulaOpacity > 0 && (
        <text
          x={1200}
          y={250}
          fill={DEBT_CURVE_COLOR}
          opacity={formulaOpacity}
          fontFamily="'JetBrains Mono', monospace"
          fontSize={14}
          transform="rotate(-15, 1200, 250)"
        >
          {formulaText.substring(0, formulaCharsVisible)}
        </text>
      )}
    </svg>
  );
};
