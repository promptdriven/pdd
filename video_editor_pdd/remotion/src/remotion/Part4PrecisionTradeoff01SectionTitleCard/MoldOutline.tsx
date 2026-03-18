import React from 'react';
import { Easing, interpolate, useCurrentFrame } from 'remotion';
import {
  COLORS,
  MOLD,
  OPACITIES,
  POSITIONS,
  TIMING,
  TYPOGRAPHY,
} from './constants';

export const MoldOutline: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame - TIMING.ghostStart;

  if (localFrame < 0) return null;

  const { x: cx, y: cy } = POSITIONS.moldOutline;
  const { width, height, strokeWidth } = MOLD;

  const halfW = width / 2;
  const halfH = height / 2;

  // Draw progress for 4 wall segments over wallDrawDuration
  const drawProgress = interpolate(
    localFrame,
    [0, TIMING.wallDrawDuration],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  // Total perimeter
  const perimeter = 2 * (width + height);
  const drawnLength = drawProgress * perimeter;

  // Build path segments: top, right, bottom, left
  const segments = [
    { length: width, x1: cx - halfW, y1: cy - halfH, x2: cx + halfW, y2: cy - halfH },
    { length: height, x1: cx + halfW, y1: cy - halfH, x2: cx + halfW, y2: cy + halfH },
    { length: width, x1: cx + halfW, y1: cy + halfH, x2: cx - halfW, y2: cy + halfH },
    { length: height, x1: cx - halfW, y1: cy + halfH, x2: cx - halfW, y2: cy - halfH },
  ];

  let remaining = drawnLength;
  const lines: React.ReactNode[] = [];

  for (let i = 0; i < segments.length; i++) {
    const seg = segments[i];
    if (remaining <= 0) break;

    const segDrawn = Math.min(remaining, seg.length);
    const t = segDrawn / seg.length;

    const endX = seg.x1 + (seg.x2 - seg.x1) * t;
    const endY = seg.y1 + (seg.y2 - seg.y1) * t;

    lines.push(
      <line
        key={`wall-${i}`}
        x1={seg.x1}
        y1={seg.y1}
        x2={endX}
        y2={endY}
        stroke={COLORS.moldOutline}
        strokeWidth={strokeWidth}
        opacity={OPACITIES.ghostMold}
        strokeLinecap="square"
      />
    );

    remaining -= seg.length;
  }

  // Steady glow after hold starts (no pulse, just steady)
  const glowLocalFrame = frame - TIMING.holdStart;
  const glowOpacity =
    glowLocalFrame >= 0
      ? OPACITIES.ghostGlow * 1.5
      : interpolate(localFrame, [0, TIMING.wallDrawDuration], [0, OPACITIES.ghostGlow], {
          extrapolateRight: 'clamp',
        });

  // Label
  const labelOpacity = interpolate(
    localFrame,
    [TIMING.wallDrawDuration - 10, TIMING.wallDrawDuration],
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
        <filter id="moldGlow">
          <feGaussianBlur stdDeviation={TIMING.glowBlur} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>
      {/* Main wall lines */}
      <g>{lines}</g>
      {/* Glow layer */}
      <g opacity={glowOpacity} filter="url(#moldGlow)">
        {lines.map((_, i) => {
          const seg = segments[i];
          if (!seg) return null;
          const segDrawn = Math.min(
            Math.max(drawnLength - segments.slice(0, i).reduce((a, s) => a + s.length, 0), 0),
            seg.length
          );
          if (segDrawn <= 0) return null;
          const t = segDrawn / seg.length;
          return (
            <line
              key={`glow-wall-${i}`}
              x1={seg.x1}
              y1={seg.y1}
              x2={seg.x1 + (seg.x2 - seg.x1) * t}
              y2={seg.y1 + (seg.y2 - seg.y1) * t}
              stroke={COLORS.moldOutline}
              strokeWidth={strokeWidth + 2}
              opacity={0.3}
              strokeLinecap="square"
            />
          );
        })}
      </g>
      {/* Label */}
      <text
        x={cx}
        y={cy + halfH + 24}
        textAnchor="middle"
        fill={COLORS.moldOutline}
        opacity={labelOpacity}
        fontFamily="Inter, sans-serif"
        fontSize={TYPOGRAPHY.ghostLabel.size}
        fontWeight={600}
      >
        WALLS ONLY
      </text>
    </svg>
  );
};
