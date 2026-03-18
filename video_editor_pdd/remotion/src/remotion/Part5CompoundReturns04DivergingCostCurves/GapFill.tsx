import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  PATCHING_COLOR,
  PDD_COLOR,
  PATCHING_POINTS,
  PDD_POINTS,
  GAP_FILL_START,
  GAP_FILL_DURATION,
  PULSE_CYCLE,
} from './constants';

/**
 * Gradient fill between the two curves, with a subtle pulsing opacity.
 * Clips to the area between patching (top) and PDD (bottom) curves.
 */
export const GapFill: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade-in for the fill
  const fadeIn = interpolate(
    frame,
    [GAP_FILL_START, GAP_FILL_START + GAP_FILL_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Pulsing opacity: cycles between 0.02 and 0.04 using sine wave
  const elapsed = Math.max(0, frame - GAP_FILL_START);
  const pulseT = (Math.sin((elapsed / PULSE_CYCLE) * Math.PI * 2) + 1) / 2;
  const pulseOpacity = 0.02 + pulseT * 0.02;

  const finalOpacity = frame < GAP_FILL_START ? 0 : fadeIn * (pulseOpacity / 0.03);

  // Build polygon path: patching curve forward, then PDD curve reversed
  const polygonPath = useMemo(() => {
    const forward = PATCHING_POINTS.map(([x, y]) => `${x},${y}`).join(' ');
    const backward = [...PDD_POINTS].reverse().map(([x, y]) => `${x},${y}`).join(' ');
    return `${forward} ${backward}`;
  }, []);

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <linearGradient id="gapGradient" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={PATCHING_COLOR} stopOpacity={0.06} />
          <stop offset="100%" stopColor={PDD_COLOR} stopOpacity={0.06} />
        </linearGradient>
      </defs>
      <polygon
        points={polygonPath}
        fill="url(#gapGradient)"
        opacity={finalOpacity}
      />
    </svg>
  );
};
