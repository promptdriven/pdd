import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, FONTS } from './constants';

interface ConnectingArrowProps {
  startFrame: number;
  from: [number, number];
  to: [number, number];
  drawDuration?: number;
}

export const ConnectingArrow: React.FC<ConnectingArrowProps> = ({
  startFrame,
  from,
  to,
  drawDuration = 25,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  const progress = interpolate(localFrame, [0, drawDuration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  const labelOpacity = interpolate(localFrame, [drawDuration - 5, drawDuration + 10], [0, 0.5], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Line endpoints
  const dx = to[0] - from[0];
  const dy = to[1] - from[1];
  const currentX = from[0] + dx * progress;
  const currentY = from[1] + dy * progress;

  // Arrow head
  const lineLength = Math.sqrt(dx * dx + dy * dy);
  const arrowSize = 8;
  const angle = Math.atan2(dy, dx);
  const a1x = currentX - arrowSize * Math.cos(angle - Math.PI / 6);
  const a1y = currentY - arrowSize * Math.sin(angle - Math.PI / 6);
  const a2x = currentX - arrowSize * Math.cos(angle + Math.PI / 6);
  const a2y = currentY - arrowSize * Math.sin(angle + Math.PI / 6);

  // Label midpoint
  const midX = (from[0] + to[0]) / 2;
  const midY = (from[1] + to[1]) / 2;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
    >
      {/* Dashed line */}
      <line
        x1={from[0]}
        y1={from[1]}
        x2={currentX}
        y2={currentY}
        stroke={COLORS.green}
        strokeWidth={2}
        strokeDasharray="6 4"
        opacity={0.3}
      />

      {/* Arrow head */}
      {progress > 0.5 && (
        <polygon
          points={`${currentX},${currentY} ${a1x},${a1y} ${a2x},${a2y}`}
          fill={COLORS.green}
          opacity={0.3 * Math.min(1, (progress - 0.5) * 2)}
        />
      )}

      {/* Label */}
      <text
        x={midX + 15}
        y={midY - 10}
        fontFamily="Inter, system-ui, sans-serif"
        fontSize={10}
        fontWeight={500}
        fill={COLORS.amber}
        opacity={labelOpacity}
      >
        Tests are the walls
      </text>
    </svg>
  );
};
