import React from 'react';
import { useCurrentFrame } from 'remotion';
import {
  COUNTER_POS,
  TOTAL_MODULES,
  BLUE_ACCENT,
  LABEL_COLOR,
} from './constants';

/**
 * Displays "N / 40 modules" in the top-right corner.
 * N updates at the start frame of each wave's completion.
 */
const AnimatedCounter: React.FC = () => {
  const frame = useCurrentFrame();

  // Counter updates at the midpoint of each wave's flash animation,
  // matching the spec's counter keyframes: 0→1, 40→3, 90→5, 140→8
  const counterKeyframes: Array<{ frame: number; value: number }> = [
    { frame: 0, value: 1 },
    { frame: 40, value: 3 },
    { frame: 90, value: 5 },
    { frame: 140, value: 8 },
  ];

  let count = 0;
  for (const kf of counterKeyframes) {
    if (frame >= kf.frame) {
      count = kf.value;
    }
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: COUNTER_POS.x,
        top: COUNTER_POS.y,
        fontFamily: 'Inter, sans-serif',
        fontSize: 14,
        color: LABEL_COLOR,
        opacity: 0.5,
        whiteSpace: 'nowrap',
      }}
    >
      <span
        style={{
          color: BLUE_ACCENT,
          fontWeight: 700,
          opacity: 0.7 / 0.5, // net 0.7 since parent is 0.5
        }}
      >
        {count}
      </span>{' '}
      / {TOTAL_MODULES} modules
    </div>
  );
};

export default AnimatedCounter;
