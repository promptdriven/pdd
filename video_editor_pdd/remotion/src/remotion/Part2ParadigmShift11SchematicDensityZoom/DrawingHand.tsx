// ============================================================
// DrawingHand.tsx – Stylized vector hand silhouette holding a pencil.
// Moves across the schematic, slows down, and fades out.
// ============================================================
import React from 'react';
import { interpolate, Easing } from 'remotion';

interface DrawingHandProps {
  frame: number;
  handColor: string;
  handOpacity: number;
  fadeOutStart: number;
  fadeOutDuration: number;
  /** Bounding box for hand movement */
  areaWidth: number;
  areaHeight: number;
}

export const DrawingHand: React.FC<DrawingHandProps> = ({
  frame,
  handColor,
  handOpacity,
  fadeOutStart,
  fadeOutDuration,
  areaWidth,
  areaHeight,
}) => {
  // Hand position — decelerating movement (easeOutCubic)
  const moveProgress = interpolate(frame, [0, 300], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(3)),
  });

  // Hand traces a path across the schematic area
  const handX = areaWidth * 0.3 + moveProgress * areaWidth * 0.35;
  const handY =
    areaHeight * 0.4 +
    Math.sin(moveProgress * Math.PI * 4) * 60 * (1 - moveProgress);

  // Pencil wobble (decreasing amplitude as hand slows)
  const wobbleAmp = (1 - moveProgress) * 6;
  const wobbleX = Math.sin(frame * 0.3) * wobbleAmp;
  const wobbleY = Math.cos(frame * 0.4) * wobbleAmp;

  // Opacity: steady, then fade out
  const opacity = interpolate(
    frame,
    [0, fadeOutStart, fadeOutStart + fadeOutDuration],
    [handOpacity, handOpacity, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(2)),
    },
  );

  if (opacity <= 0.01) return null;

  return (
    <svg
      width={120}
      height={140}
      style={{
        position: 'absolute',
        left: handX + wobbleX - 40,
        top: handY + wobbleY - 80,
        opacity,
        pointerEvents: 'none',
      }}
      viewBox="0 0 120 140"
    >
      {/* Pencil */}
      <line
        x1={45}
        y1={10}
        x2={60}
        y2={70}
        stroke={handColor}
        strokeWidth={4}
        strokeLinecap="round"
      />
      {/* Pencil tip */}
      <polygon points="58,66 62,66 60,78" fill={handColor} />

      {/* Simplified hand shape */}
      <path
        d={`
          M 40 70
          C 35 65, 30 68, 32 75
          L 30 90
          C 28 95, 30 100, 35 100
          L 50 105
          C 55 108, 60 110, 65 108
          L 80 100
          C 88 96, 90 90, 85 84
          L 78 78
          C 75 72, 68 68, 60 70
          Z
        `}
        fill={handColor}
        opacity={0.85}
      />

      {/* Fingers curled around pencil */}
      <path
        d={`
          M 48 72
          C 50 68, 55 66, 58 68
          M 52 75
          C 54 71, 58 70, 61 72
        `}
        stroke={handColor}
        strokeWidth={2}
        fill="none"
        opacity={0.7}
      />
    </svg>
  );
};
