import React, { useMemo } from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  CURVE_ORIGIN,
  AMBER_END,
  BLUE_END,
  AMBER_CURVE,
  BLUE_CURVE,
  CURVE_STROKE_WIDTH,
  CURVE_OPACITY,
  CURVE_GLOW_BLUR,
  CURVE_GLOW_OPACITY,
  ORIGIN_DOT_OPACITY,
  TITLE_COLOR,
  CURVE_START,
  CURVE_DURATION,
  PULSE_CYCLE,
} from './constants';

/**
 * Builds an SVG path for an exponential-style curve from origin to end.
 * The amber (debt) curve sweeps upward via a control point high-right.
 * The blue (PDD) curve drifts gently lower-right via a flatter control point.
 */
function buildCurvePath(
  origin: [number, number],
  end: [number, number],
  direction: 'up' | 'flat',
): string {
  const [ox, oy] = origin;
  const [ex, ey] = end;
  const midX = (ox + ex) / 2;

  if (direction === 'up') {
    // Exponential rise — control point pulls strongly upward
    const cp1x = ox + (ex - ox) * 0.3;
    const cp1y = oy;
    const cp2x = midX;
    const cp2y = ey - (oy - ey) * 0.4;
    return `M${ox},${oy} C${cp1x},${cp1y} ${cp2x},${cp2y} ${ex},${ey}`;
  }

  // Flat trajectory — control point stays near horizontal
  const cp1x = ox + (ex - ox) * 0.4;
  const cp1y = oy + 5;
  const cp2x = midX + (ex - midX) * 0.3;
  const cp2y = ey - 10;
  return `M${ox},${oy} C${cp1x},${cp1y} ${cp2x},${cp2y} ${ex},${ey}`;
}

export const DivergingCurves: React.FC = () => {
  const frame = useCurrentFrame();

  const amberPath = useMemo(
    () => buildCurvePath(CURVE_ORIGIN, AMBER_END, 'up'),
    [],
  );
  const bluePath = useMemo(
    () => buildCurvePath(CURVE_ORIGIN, BLUE_END, 'flat'),
    [],
  );

  // Approximate path length for dash animation
  const pathLength = 600;

  // Draw progress: curves start drawing at CURVE_START and finish over CURVE_DURATION
  const localFrame = frame - CURVE_START;
  const drawProgress = interpolate(
    localFrame,
    [0, CURVE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.bezier(0.42, 0, 0.58, 1), // easeInOut(cubic)
    },
  );

  const dashOffset = pathLength * (1 - drawProgress);

  // Gentle divergence pulse after curves are drawn (frame 90-120)
  const pulseFrame = frame - 90;
  const pulseOpacity =
    pulseFrame >= 0
      ? interpolate(
          pulseFrame % PULSE_CYCLE,
          [0, PULSE_CYCLE / 2, PULSE_CYCLE],
          [0, 0.015, 0],
          {
            extrapolateRight: 'clamp',
            easing: Easing.bezier(0.37, 0, 0.63, 1), // easeInOut(sine approx)
          },
        )
      : 0;

  // Fade-in for the whole SVG alongside background (frames 0-15)
  const svgOpacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0, opacity: svgOpacity }}
    >
      <defs>
        <filter id="amber-glow">
          <feGaussianBlur stdDeviation={CURVE_GLOW_BLUR} />
        </filter>
        <filter id="blue-glow">
          <feGaussianBlur stdDeviation={CURVE_GLOW_BLUR} />
        </filter>
      </defs>

      {/* Glow layers */}
      <path
        d={amberPath}
        fill="none"
        stroke={AMBER_CURVE}
        strokeWidth={CURVE_STROKE_WIDTH + 4}
        strokeOpacity={CURVE_GLOW_OPACITY + pulseOpacity}
        strokeDasharray={pathLength}
        strokeDashoffset={dashOffset}
        filter="url(#amber-glow)"
      />
      <path
        d={bluePath}
        fill="none"
        stroke={BLUE_CURVE}
        strokeWidth={CURVE_STROKE_WIDTH + 4}
        strokeOpacity={CURVE_GLOW_OPACITY + pulseOpacity}
        strokeDasharray={pathLength}
        strokeDashoffset={dashOffset}
        filter="url(#blue-glow)"
      />

      {/* Main curve strokes */}
      <path
        d={amberPath}
        fill="none"
        stroke={AMBER_CURVE}
        strokeWidth={CURVE_STROKE_WIDTH}
        strokeOpacity={CURVE_OPACITY}
        strokeDasharray={pathLength}
        strokeDashoffset={dashOffset}
        strokeLinecap="round"
      />
      <path
        d={bluePath}
        fill="none"
        stroke={BLUE_CURVE}
        strokeWidth={CURVE_STROKE_WIDTH}
        strokeOpacity={CURVE_OPACITY}
        strokeDasharray={pathLength}
        strokeDashoffset={dashOffset}
        strokeLinecap="round"
      />

      {/* Shared origin dot */}
      <circle
        cx={CURVE_ORIGIN[0]}
        cy={CURVE_ORIGIN[1]}
        r={3}
        fill={TITLE_COLOR}
        opacity={ORIGIN_DOT_OPACITY * drawProgress}
      />
    </svg>
  );
};
