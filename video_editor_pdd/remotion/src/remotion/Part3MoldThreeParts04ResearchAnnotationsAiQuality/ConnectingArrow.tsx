import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, FONT } from './constants';

interface ConnectingArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  startFrame: number;
  drawDuration?: number;
  label?: string;
}

export const ConnectingArrow: React.FC<ConnectingArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  startFrame,
  drawDuration = 25,
  label = 'Tests are the walls',
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  const drawProgress = interpolate(localFrame, [0, drawDuration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  const labelOpacity = interpolate(
    localFrame,
    [drawDuration * 0.6, drawDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Calculate line length for dash animation
  const dx = toX - fromX;
  const dy = toY - fromY;
  const lineLength = Math.sqrt(dx * dx + dy * dy);

  // Calculate midpoint for label
  const midX = (fromX + toX) / 2;
  const midY = (fromY + toY) / 2;

  // Calculate angle for arrowhead
  const angle = Math.atan2(dy, dx);
  const arrowSize = 10;

  // Current endpoint based on draw progress
  const curX = fromX + dx * drawProgress;
  const curY = fromY + dy * drawProgress;

  // Arrowhead points
  const arrowAngle1 = angle + Math.PI * 0.8;
  const arrowAngle2 = angle - Math.PI * 0.8;
  const ax1 = curX + arrowSize * Math.cos(arrowAngle1);
  const ay1 = curY + arrowSize * Math.sin(arrowAngle1);
  const ax2 = curX + arrowSize * Math.cos(arrowAngle2);
  const ay2 = curY + arrowSize * Math.sin(arrowAngle2);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
    >
      {/* Dashed line */}
      <line
        x1={fromX}
        y1={fromY}
        x2={curX}
        y2={curY}
        stroke={COLORS.green}
        strokeWidth={2}
        strokeOpacity={0.3}
        strokeDasharray="6 4"
      />

      {/* Arrowhead */}
      {drawProgress > 0.3 && (
        <polygon
          points={`${curX},${curY} ${ax1},${ay1} ${ax2},${ay2}`}
          fill={COLORS.green}
          fillOpacity={0.3 * drawProgress}
        />
      )}

      {/* Label */}
      <text
        x={midX - 20}
        y={midY - 10}
        fill={COLORS.amber}
        opacity={labelOpacity * 0.5}
        fontSize={10}
        fontFamily={FONT.family}
        fontWeight={500}
      >
        {label}
      </text>
    </svg>
  );
};
