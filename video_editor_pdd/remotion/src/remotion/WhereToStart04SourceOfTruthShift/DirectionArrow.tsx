import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TIMING, LAYOUT } from './constants';

/**
 * Curved arrow that starts pointing left→right (extraction)
 * and reverses to right→left (generation) at the specified frame.
 */
export const DirectionArrow: React.FC = () => {
  const frame = useCurrentFrame();

  const { arrowFrom, arrowTo } = LAYOUT;

  // Arrow rotation: 0 = pointing right (L→R), 180 = pointing left (R→L)
  const rotation = interpolate(
    frame,
    [
      TIMING.arrowReverseStart,
      TIMING.arrowReverseStart + TIMING.arrowReverseDuration,
    ],
    [0, 180],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const midX = (arrowFrom.x + arrowTo.x) / 2;
  const midY = arrowFrom.y;
  const arrowWidth = arrowTo.x - arrowFrom.x;
  const arrowHeight = 60;

  // SVG path for the curved arrow
  const svgWidth = arrowWidth + 40;
  const svgHeight = arrowHeight + 40;
  const padX = 20;
  const padY = 20;

  // Curved path from left to right
  const startX = padX;
  const startY = padY + arrowHeight / 2;
  const endX = padX + arrowWidth;
  const endY = padY + arrowHeight / 2;
  const ctrlY = padY - 10; // curve upward

  const headSize = 8;

  return (
    <div
      style={{
        position: 'absolute',
        left: midX - svgWidth / 2,
        top: midY - svgHeight / 2,
        width: svgWidth,
        height: svgHeight,
        transform: `rotate(${rotation}deg)`,
        transformOrigin: 'center center',
      }}
    >
      <svg width={svgWidth} height={svgHeight} viewBox={`0 0 ${svgWidth} ${svgHeight}`}>
        {/* Curved line */}
        <path
          d={`M ${startX} ${startY} Q ${padX + arrowWidth / 2} ${ctrlY} ${endX} ${endY}`}
          fill="none"
          stroke={COLORS.arrow}
          strokeWidth={2}
          opacity={0.4}
        />
        {/* Arrowhead at the end */}
        <polygon
          points={`
            ${endX},${endY}
            ${endX - headSize * 1.5},${endY - headSize}
            ${endX - headSize * 1.5},${endY + headSize}
          `}
          fill={COLORS.arrow}
          opacity={0.4}
        />
      </svg>
    </div>
  );
};

export default DirectionArrow;
