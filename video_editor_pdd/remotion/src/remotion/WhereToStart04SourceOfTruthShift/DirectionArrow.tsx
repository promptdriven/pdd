import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TIMING } from './constants';

interface DirectionArrowProps {
  startX: number;
  endX: number;
  y: number;
}

/**
 * A horizontal curved arrow that reverses direction mid-animation.
 * Initially points left→right (extraction). At reverseFrame, rotates 180°
 * so it points right→left (generation).
 */
const DirectionArrow: React.FC<DirectionArrowProps> = ({ startX, endX, y }) => {
  const frame = useCurrentFrame();

  const rotation = interpolate(
    frame,
    [TIMING.arrowReverseStart, TIMING.arrowReverseStart + TIMING.arrowReverseDuration],
    [0, 180],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const midX = (startX + endX) / 2;
  const arrowWidth = endX - startX;
  const headSize = 8;

  return (
    <div
      style={{
        position: 'absolute',
        left: midX - arrowWidth / 2,
        top: y - 20,
        width: arrowWidth,
        height: 40,
        transform: `rotate(${rotation}deg)`,
        transformOrigin: 'center center',
      }}
    >
      <svg
        width={arrowWidth}
        height={40}
        viewBox={`0 0 ${arrowWidth} 40`}
        style={{ overflow: 'visible' }}
      >
        {/* Curved arrow path */}
        <path
          d={`M 20 20 Q ${arrowWidth / 2} 6, ${arrowWidth - 20 - headSize} 20`}
          fill="none"
          stroke={COLORS.promptBlue}
          strokeWidth={2}
          strokeOpacity={0.4}
        />
        {/* Arrowhead (pointing right) */}
        <polygon
          points={`${arrowWidth - 20 - headSize},${20 - headSize} ${arrowWidth - 20},20 ${arrowWidth - 20 - headSize},${20 + headSize}`}
          fill={COLORS.promptBlue}
          fillOpacity={0.4}
        />
        {/* Small tail circle */}
        <circle
          cx={20}
          cy={20}
          r={3}
          fill={COLORS.promptBlue}
          fillOpacity={0.3}
        />
      </svg>
    </div>
  );
};

export default DirectionArrow;
