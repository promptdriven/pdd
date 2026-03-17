import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  REGEN_COLOR,
  SAWTOOTH_DRAW_START,
  SAWTOOTH_DRAW_DURATION,
  SAWTOOTH_BASELINE_Y,
  buildSawtoothPixels,
} from './constants';

function pointsToPath(points: { x: number; y: number }[]): string {
  if (points.length === 0) return '';
  let d = `M ${points[0].x} ${points[0].y}`;
  for (let i = 1; i < points.length; i++) {
    d += ` L ${points[i].x} ${points[i].y}`;
  }
  return d;
}

function computePathLength(points: { x: number; y: number }[]): number {
  let total = 0;
  for (let i = 1; i < points.length; i++) {
    const dx = points[i].x - points[i - 1].x;
    const dy = points[i].y - points[i - 1].y;
    total += Math.sqrt(dx * dx + dy * dy);
  }
  return total;
}

// Find x positions where the sawtooth resets (falls back to baseline)
function getResetXPositions(points: { x: number; y: number }[]): number[] {
  const resets: number[] = [];
  for (let i = 2; i < points.length; i++) {
    // A reset is where the y goes from peak back to baseline
    if (
      points[i].y === SAWTOOTH_BASELINE_Y &&
      points[i - 1].y < SAWTOOTH_BASELINE_Y
    ) {
      resets.push(points[i].x);
    }
  }
  return resets;
}

export const SawtoothLine: React.FC = () => {
  const frame = useCurrentFrame();
  const sawtoothPoints = useMemo(() => buildSawtoothPixels(), []);
  const pathD = useMemo(() => pointsToPath(sawtoothPoints), [sawtoothPoints]);
  const totalLength = useMemo(
    () => computePathLength(sawtoothPoints),
    [sawtoothPoints],
  );
  const resetXPositions = useMemo(
    () => getResetXPositions(sawtoothPoints),
    [sawtoothPoints],
  );

  const drawProgress = interpolate(
    frame,
    [SAWTOOTH_DRAW_START, SAWTOOTH_DRAW_START + SAWTOOTH_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  const visibleLength = drawProgress * totalLength;
  const hiddenLength = totalLength - visibleLength;

  // Label fade in after sawtooth is mostly drawn
  const labelOpacity = interpolate(
    frame,
    [
      SAWTOOTH_DRAW_START + SAWTOOTH_DRAW_DURATION - 20,
      SAWTOOTH_DRAW_START + SAWTOOTH_DRAW_DURATION + 10,
    ],
    [0, 0.5],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Dashed reset line opacity
  const resetLineOpacity = interpolate(
    frame,
    [
      SAWTOOTH_DRAW_START + SAWTOOTH_DRAW_DURATION * 0.3,
      SAWTOOTH_DRAW_START + SAWTOOTH_DRAW_DURATION,
    ],
    [0, 0.08],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  if (drawProgress <= 0) return null;

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Dashed vertical lines at reset points */}
      {resetXPositions.map((x, i) => (
        <line
          key={`reset-${i}`}
          x1={x}
          y1={200}
          x2={x}
          y2={800}
          stroke={REGEN_COLOR}
          strokeWidth={1}
          strokeDasharray="6 4"
          opacity={resetLineOpacity}
        />
      ))}

      {/* Sawtooth line */}
      <path
        d={pathD}
        fill="none"
        stroke={REGEN_COLOR}
        strokeWidth={2}
        strokeDasharray={totalLength}
        strokeDashoffset={hiddenLength}
        strokeLinecap="round"
      />

      {/* Label at the end of the line */}
      {labelOpacity > 0 && (
        <text
          x={1710}
          y={SAWTOOTH_BASELINE_Y - 10}
          fill={REGEN_COLOR}
          opacity={labelOpacity}
          fontFamily="Inter, sans-serif"
          fontSize={12}
          textAnchor="end"
        >
          Regeneration cost (resets each cycle)
        </text>
      )}
    </svg>
  );
};
