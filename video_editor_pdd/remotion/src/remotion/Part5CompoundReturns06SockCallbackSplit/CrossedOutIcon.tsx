import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { ICON_APPEAR_START, ICON_APPEAR_DURATION } from './constants';

interface CrossedOutIconProps {
  type: 'needle' | 'patch';
  color: string;
  opacity: number;
  x: number;
  y: number;
}

/**
 * A small icon (darning needle or patch) with a diagonal strike-through line.
 */
export const CrossedOutIcon: React.FC<CrossedOutIconProps> = ({
  type,
  color,
  opacity,
  x,
  y,
}) => {
  const frame = useCurrentFrame();

  const scale = interpolate(
    frame,
    [ICON_APPEAR_START, ICON_APPEAR_START + ICON_APPEAR_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  const iconSize = 28;

  return (
    <div
      style={{
        position: 'absolute',
        left: x - iconSize / 2,
        top: y - iconSize / 2,
        width: iconSize,
        height: iconSize,
        opacity,
        transform: `scale(${scale})`,
        transformOrigin: 'center center',
      }}
    >
      <svg
        width={iconSize}
        height={iconSize}
        viewBox="0 0 28 28"
        fill="none"
        xmlns="http://www.w3.org/2000/svg"
      >
        {type === 'needle' ? (
          /* Darning needle icon */
          <>
            {/* Needle body */}
            <line
              x1="6"
              y1="22"
              x2="22"
              y2="6"
              stroke={color}
              strokeWidth="2"
              strokeLinecap="round"
            />
            {/* Needle eye */}
            <circle cx="21" cy="7" r="2" stroke={color} strokeWidth="1.5" fill="none" />
            {/* Thread hint */}
            <path
              d="M23 5 Q26 2 24 0"
              stroke={color}
              strokeWidth="1"
              strokeLinecap="round"
              fill="none"
              opacity={0.6}
            />
          </>
        ) : (
          /* Patch icon */
          <>
            {/* Patch square */}
            <rect
              x="7"
              y="7"
              width="14"
              height="14"
              rx="2"
              stroke={color}
              strokeWidth="1.5"
              fill="none"
            />
            {/* Stitch marks */}
            <line x1="7" y1="10" x2="21" y2="10" stroke={color} strokeWidth="0.8" strokeDasharray="2 2" />
            <line x1="7" y1="14" x2="21" y2="14" stroke={color} strokeWidth="0.8" strokeDasharray="2 2" />
            <line x1="7" y1="18" x2="21" y2="18" stroke={color} strokeWidth="0.8" strokeDasharray="2 2" />
          </>
        )}
        {/* Strike-through diagonal line */}
        <line
          x1="4"
          y1="24"
          x2="24"
          y2="4"
          stroke={color}
          strokeWidth="2"
          strokeLinecap="round"
        />
      </svg>
    </div>
  );
};
