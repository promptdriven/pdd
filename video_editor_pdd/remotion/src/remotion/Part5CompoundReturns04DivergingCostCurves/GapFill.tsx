import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CHART,
  TIMING,
  COLORS,
  PATCHING_POINTS,
  PDD_POINTS,
  pointsToPath,
} from './constants';

export const GapFill: React.FC = () => {
  const frame = useCurrentFrame();

  const localFrame = frame - TIMING.gapFillStart;
  if (localFrame < 0) return null;

  // Fade in the fill
  const fadeIn = interpolate(
    localFrame,
    [0, 30],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Pulsing opacity cycle (60 frames)
  const pulsePhase = ((localFrame % 60) / 60) * Math.PI * 2;
  const pulseOpacity = interpolate(
    Math.sin(pulsePhase),
    [-1, 1],
    [0.02, 0.04],
  );

  const opacity = fadeIn * pulseOpacity;

  // Build the closed polygon path:
  // Go along patching curve forward, then PDD curve backward
  const patchPath = pointsToPath(PATCHING_POINTS);
  const pddReversed = [...PDD_POINTS].reverse();
  const pddBackPath = pddReversed
    .map((p, i) => {
      if (i === 0) return `L ${p[0]} ${p[1]}`;
      const prev = pddReversed[i - 1];
      const cpX = (prev[0] + p[0]) / 2;
      return `C ${cpX} ${prev[1]}, ${cpX} ${p[1]}, ${p[0]} ${p[1]}`;
    })
    .join(' ');

  const fillPath = `${patchPath} ${pddBackPath} Z`;
  const gradientId = 'gap-gradient';

  return (
    <svg
      width={CHART.width}
      height={CHART.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <linearGradient id={gradientId} x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={COLORS.patching} stopOpacity={1} />
          <stop offset="100%" stopColor={COLORS.pdd} stopOpacity={1} />
        </linearGradient>
      </defs>
      <path
        d={fillPath}
        fill={`url(#${gradientId})`}
        opacity={opacity}
      />
    </svg>
  );
};
