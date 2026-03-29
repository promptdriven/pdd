import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { ARROW_COLOR, ARROW_OPACITY, ARROW_DRAW_DURATION } from './constants';

interface ConnectionArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  dashed: boolean;
  drawStartFrame: number;
  arrowOpacity: number;
}

export const ConnectionArrow: React.FC<ConnectionArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  dashed,
  drawStartFrame,
  arrowOpacity,
}) => {
  const frame = useCurrentFrame();

  const dx = toX - fromX;
  const dy = toY - fromY;
  const length = Math.sqrt(dx * dx + dy * dy);

  // Shorten line to not overlap with module boxes
  const shortenStart = 50;
  const shortenEnd = 50;
  const nx = dx / length;
  const ny = dy / length;

  const startX = fromX + nx * shortenStart;
  const startY = fromY + ny * shortenStart;
  const endX = toX - nx * shortenEnd;
  const endY = toY - ny * shortenEnd;

  // Draw animation progress
  const drawProgress = interpolate(
    frame,
    [drawStartFrame, drawStartFrame + ARROW_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  if (drawProgress <= 0) return null;

  // Arrowhead
  const arrowSize = 8;
  const angle = Math.atan2(endY - startY, endX - startX);
  const arrowX1 =
    endX - arrowSize * Math.cos(angle - Math.PI / 6);
  const arrowY1 =
    endY - arrowSize * Math.sin(angle - Math.PI / 6);
  const arrowX2 =
    endX - arrowSize * Math.cos(angle + Math.PI / 6);
  const arrowY2 =
    endY - arrowSize * Math.sin(angle + Math.PI / 6);

  return (
    <g opacity={arrowOpacity * ARROW_OPACITY}>
      <line
        x1={startX}
        y1={startY}
        x2={startX + (endX - startX) * drawProgress}
        y2={startY + (endY - startY) * drawProgress}
        stroke={ARROW_COLOR}
        strokeWidth={1.5}
        strokeDasharray={dashed ? '6 4' : 'none'}
      />
      {drawProgress > 0.9 && (
        <polygon
          points={`${endX},${endY} ${arrowX1},${arrowY1} ${arrowX2},${arrowY2}`}
          fill={ARROW_COLOR}
          opacity={interpolate(drawProgress, [0.9, 1], [0, 1], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          })}
        />
      )}
    </g>
  );
};
