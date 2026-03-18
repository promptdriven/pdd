import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { WIRE_COLOR } from './constants';

interface FlowArrowProps {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
  startFrame: number;
  drawDuration?: number;
  color?: string;
  opacity?: number;
}

/**
 * An animated arrow that draws itself from point A to point B.
 */
export const FlowArrow: React.FC<FlowArrowProps> = ({
  x1,
  y1,
  x2,
  y2,
  startFrame,
  drawDuration = 20,
  color = WIRE_COLOR,
  opacity = 0.3,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  const progress = interpolate(localFrame, [0, drawDuration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  const dx = x2 - x1;
  const dy = y2 - y1;
  const currentX2 = x1 + dx * progress;
  const currentY2 = y1 + dy * progress;

  // Arrowhead
  const arrowSize = 6;
  const angle = Math.atan2(dy, dx);
  const arrowX1 = currentX2 - arrowSize * Math.cos(angle - 0.4);
  const arrowY1 = currentY2 - arrowSize * Math.sin(angle - 0.4);
  const arrowX2 = currentX2 - arrowSize * Math.cos(angle + 0.4);
  const arrowY2 = currentY2 - arrowSize * Math.sin(angle + 0.4);

  return (
    <svg
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
        pointerEvents: 'none',
      }}
    >
      <line
        x1={x1}
        y1={y1}
        x2={currentX2}
        y2={currentY2}
        stroke={color}
        strokeWidth={1}
        opacity={opacity}
      />
      {progress > 0.5 && (
        <polygon
          points={`${currentX2},${currentY2} ${arrowX1},${arrowY1} ${arrowX2},${arrowY2}`}
          fill={color}
          opacity={opacity}
        />
      )}
    </svg>
  );
};
