import React from 'react';
import { Easing, interpolate, useCurrentFrame } from 'remotion';
import {
  COLORS,
  DOT_GRID,
  OPACITIES,
  POSITIONS,
  TIMING,
  TYPOGRAPHY,
} from './constants';

export const StaggerDots: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame - TIMING.ghostStart;

  if (localFrame < 0) return null;

  const { rows, cols, dotSize, spacing } = DOT_GRID;
  const { x: cx, y: cy } = POSITIONS.dotGrid;

  const gridWidth = (cols - 1) * spacing;
  const gridHeight = (rows - 1) * spacing;
  const startX = cx - gridWidth / 2;
  const startY = cy - gridHeight / 2;

  const totalDots = rows * cols;

  // Pulse effect after hold starts
  const pulseLocalFrame = frame - TIMING.holdStart;
  const pulseMultiplier =
    pulseLocalFrame >= 0
      ? interpolate(
          pulseLocalFrame % TIMING.pulseCycleFrames,
          [0, TIMING.pulseCycleFrames / 2, TIMING.pulseCycleFrames],
          [1, 1.6, 1],
          { extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
        )
      : 1;

  const dots: React.ReactNode[] = [];
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const index = r * cols + c;
      // Each dot appears 1 frame after the previous
      const dotOpacity = interpolate(
        localFrame,
        [index, index + 1],
        [0, OPACITIES.ghostDots * pulseMultiplier],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
      );

      if (dotOpacity <= 0) continue;

      dots.push(
        <circle
          key={`dot-${r}-${c}`}
          cx={startX + c * spacing}
          cy={startY + r * spacing}
          r={dotSize / 2}
          fill={COLORS.dotGrid}
          opacity={dotOpacity}
        />
      );
    }
  }

  // Glow filter
  const glowOpacity = interpolate(
    localFrame,
    [0, totalDots],
    [0, OPACITIES.ghostGlow],
    { extrapolateRight: 'clamp' }
  );

  // Label opacity
  const labelOpacity = interpolate(
    localFrame,
    [totalDots - 10, totalDots],
    [0, OPACITIES.ghostLabel],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id="dotGlow">
          <feGaussianBlur stdDeviation={TIMING.glowBlur} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>
      <g filter="url(#dotGlow)" opacity={glowOpacity > 0 ? 1 : 1}>
        {dots}
      </g>
      {/* Glow layer */}
      <g opacity={glowOpacity}>
        {dots.map((_, i) => {
          const r = Math.floor(i / cols);
          const c = i % cols;
          return (
            <circle
              key={`glow-${r}-${c}`}
              cx={startX + c * spacing}
              cy={startY + r * spacing}
              r={dotSize}
              fill={COLORS.dotGrid}
              opacity={0.3}
              filter="url(#dotGlow)"
            />
          );
        })}
      </g>
      {/* Label */}
      <text
        x={cx}
        y={cy + gridHeight / 2 + 24}
        textAnchor="middle"
        fill={COLORS.dotGrid}
        opacity={labelOpacity}
        fontFamily="Inter, sans-serif"
        fontSize={TYPOGRAPHY.ghostLabel.size}
        fontWeight={600}
      >
        EVERY POINT
      </text>
    </svg>
  );
};
