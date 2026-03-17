import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  DOT_MATRIX,
  POSITIONS,
  COLORS,
  GHOST_LABEL,
  TIMING,
} from './constants';

export const StaggerDots: React.FC<{ startFrame: number }> = ({
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const relFrame = frame - startFrame;

  const { ROWS, COLS, DOT_SIZE, SPACING, OPACITY, GLOW_BLUR, GLOW_OPACITY } =
    DOT_MATRIX;
  const { x: cx, y: cy } = POSITIONS.DOT_GRID;

  const totalWidth = (COLS - 1) * SPACING;
  const totalHeight = (ROWS - 1) * SPACING;
  const startX = cx - totalWidth / 2;
  const startY = cy - totalHeight / 2;

  const dots: React.ReactNode[] = [];
  let dotIndex = 0;

  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      const dotAppearFrame = dotIndex * TIMING.GHOST_DOTS_STAGGER;
      const dotOpacity =
        relFrame >= dotAppearFrame
          ? interpolate(relFrame - dotAppearFrame, [0, 8], [0, 1], {
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            })
          : 0;

      // Pulse effect after frame 90
      const pulsePhase =
        frame >= TIMING.HOLD_START
          ? interpolate(
              (frame - TIMING.HOLD_START) % TIMING.PULSE_CYCLE,
              [0, TIMING.PULSE_CYCLE / 2, TIMING.PULSE_CYCLE],
              [1, 1.5, 1],
              { easing: Easing.inOut(Easing.sin) }
            )
          : 1;

      const dx = startX + c * SPACING;
      const dy = startY + r * SPACING;

      dots.push(
        <circle
          key={`dot-${r}-${c}`}
          cx={dx}
          cy={dy}
          r={(DOT_SIZE / 2) * pulsePhase}
          fill={COLORS.DOT_GRID}
          opacity={OPACITY * dotOpacity}
        />
      );

      dotIndex++;
    }
  }

  const overallOpacity = relFrame < 0 ? 0 : 1;

  return (
    <g opacity={overallOpacity}>
      <defs>
        <filter id="dot-glow">
          <feGaussianBlur stdDeviation={GLOW_BLUR} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>
      <g filter="url(#dot-glow)" opacity={1}>
        {dots}
      </g>
      {/* Ghost label */}
      <text
        x={cx}
        y={startY + totalHeight + 24}
        textAnchor="middle"
        fontFamily="Inter, sans-serif"
        fontSize={GHOST_LABEL.FONT_SIZE}
        fontWeight={600}
        fill={COLORS.DOT_GRID}
        opacity={
          GHOST_LABEL.OPACITY *
          (relFrame > 0
            ? interpolate(relFrame, [0, 20], [0, 1], {
                extrapolateRight: 'clamp',
              })
            : 0)
        }
        letterSpacing={2}
      >
        {DOT_MATRIX.LABEL}
      </text>
    </g>
  );
};
