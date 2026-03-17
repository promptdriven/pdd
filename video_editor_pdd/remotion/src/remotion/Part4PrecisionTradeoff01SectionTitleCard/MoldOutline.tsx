import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  MOLD,
  POSITIONS,
  COLORS,
  GHOST_LABEL,
  TIMING,
} from './constants';

export const MoldOutline: React.FC<{ startFrame: number }> = ({
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const relFrame = frame - startFrame;

  const { x: cx, y: cy } = POSITIONS.MOLD_OUTLINE;
  const { WIDTH, HEIGHT, STROKE_WIDTH, OPACITY, GLOW_BLUR } = MOLD;

  const halfW = WIDTH / 2;
  const halfH = HEIGHT / 2;

  // Four wall segments as a rectangular path
  // Total perimeter = 2*(WIDTH + HEIGHT) = 2*(80+60) = 280
  const perimeter = 2 * (WIDTH + HEIGHT);

  const drawProgress =
    relFrame < 0
      ? 0
      : interpolate(relFrame, [0, TIMING.GHOST_WALL_DURATION], [0, 1], {
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.cubic),
        });

  // Steady glow after hold
  const glowOpacity =
    frame >= TIMING.HOLD_START
      ? interpolate(
          (frame - TIMING.HOLD_START) % TIMING.PULSE_CYCLE,
          [0, TIMING.PULSE_CYCLE / 2, TIMING.PULSE_CYCLE],
          [MOLD.GLOW_OPACITY, MOLD.GLOW_OPACITY * 2, MOLD.GLOW_OPACITY],
          { easing: Easing.inOut(Easing.sin) }
        )
      : MOLD.GLOW_OPACITY;

  const overallOpacity = relFrame < 0 ? 0 : 1;

  const rectPath = `M ${cx - halfW} ${cy - halfH}
    L ${cx + halfW} ${cy - halfH}
    L ${cx + halfW} ${cy + halfH}
    L ${cx - halfW} ${cy + halfH} Z`;

  return (
    <g opacity={overallOpacity}>
      <defs>
        <filter id="mold-glow">
          <feGaussianBlur stdDeviation={GLOW_BLUR} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>
      {/* Glow layer */}
      <path
        d={rectPath}
        fill="none"
        stroke={COLORS.MOLD_OUTLINE}
        strokeWidth={STROKE_WIDTH + 4}
        opacity={glowOpacity * drawProgress}
        strokeDasharray={perimeter}
        strokeDashoffset={perimeter * (1 - drawProgress)}
        filter="url(#mold-glow)"
      />
      {/* Main outline */}
      <path
        d={rectPath}
        fill="none"
        stroke={COLORS.MOLD_OUTLINE}
        strokeWidth={STROKE_WIDTH}
        opacity={OPACITY * drawProgress}
        strokeDasharray={perimeter}
        strokeDashoffset={perimeter * (1 - drawProgress)}
        strokeLinejoin="miter"
      />
      {/* Ghost label */}
      <text
        x={cx}
        y={cy + halfH + 24}
        textAnchor="middle"
        fontFamily="Inter, sans-serif"
        fontSize={GHOST_LABEL.FONT_SIZE}
        fontWeight={600}
        fill={COLORS.MOLD_OUTLINE}
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
        {MOLD.LABEL}
      </text>
    </g>
  );
};
