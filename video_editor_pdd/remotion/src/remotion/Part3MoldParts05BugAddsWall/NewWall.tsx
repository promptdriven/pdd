import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  NEW_WALL,
  WALL_BLUE,
  WALL_LABEL_TEXT,
} from './constants';

const SLIDE_DURATION = 40;
// Slight overshoot using back easing
const OVERSHOOT_EASING = Easing.out(Easing.back(1.4));

export const NewWall: React.FC = () => {
  const frame = useCurrentFrame();

  // Wall slides in from the right (+200px) with overshoot
  const slideX = interpolate(
    frame,
    [0, SLIDE_DURATION],
    [200, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: OVERSHOOT_EASING,
    }
  );

  // Wall opacity
  const wallOpacity = interpolate(
    frame,
    [0, 10],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Glow pulse on arrival (frame 40–70 relative to this component)
  const glowOpacity = interpolate(
    frame,
    [SLIDE_DURATION, SLIDE_DURATION + 10, SLIDE_DURATION + 30],
    [0, 0.5, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Label fade in after wall arrives
  const labelOpacity = interpolate(
    frame,
    [SLIDE_DURATION + 10, SLIDE_DURATION + 25],
    [0, 0.9],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <>
      {/* Wall segment */}
      <div
        style={{
          position: 'absolute',
          left: NEW_WALL.x + slideX,
          top: NEW_WALL.y,
          width: NEW_WALL.width,
          height: NEW_WALL.height,
          backgroundColor: WALL_BLUE,
          borderRadius: 3,
          opacity: wallOpacity,
          boxShadow: glowOpacity > 0
            ? `0 0 15px ${WALL_BLUE}${Math.round(glowOpacity * 255).toString(16).padStart(2, '0')}`
            : 'none',
        }}
      />

      {/* Label pill */}
      <div
        style={{
          position: 'absolute',
          left: NEW_WALL.x + slideX - 50,
          top: NEW_WALL.y + NEW_WALL.height + 10,
          opacity: labelOpacity,
          display: 'flex',
          justifyContent: 'center',
        }}
      >
        <div
          style={{
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 14,
            color: WALL_LABEL_TEXT,
            backgroundColor: `${WALL_BLUE}26`,
            padding: '4px 12px',
            borderRadius: 12,
            whiteSpace: 'nowrap',
            border: `1px solid ${WALL_BLUE}40`,
          }}
        >
          {NEW_WALL.label}
        </div>
      </div>
    </>
  );
};
