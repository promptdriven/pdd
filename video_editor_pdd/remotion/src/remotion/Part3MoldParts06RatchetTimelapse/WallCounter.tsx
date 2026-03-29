import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COUNTER_LABEL_COLOR,
  COUNTER_NUMBER_COLOR,
  COUNTER_PULSE_FRAMES,
  WALL_CYCLES,
  FLASH_FRAMES,
} from './constants';

export const WallCounter: React.FC = () => {
  const frame = useCurrentFrame();

  // Count starts at 5, increments when each wall finishes its flash
  const baseCount = 5;
  let currentCount = baseCount;
  let lastIncrementFrame = -100;

  for (const cycle of WALL_CYCLES) {
    const incrementFrame = cycle.startFrame + FLASH_FRAMES;
    if (frame >= incrementFrame) {
      currentCount++;
      lastIncrementFrame = incrementFrame;
    }
  }

  // Scale pulse when counter increments
  const pulseLocalFrame = frame - lastIncrementFrame;
  const scale =
    pulseLocalFrame >= 0 && pulseLocalFrame < COUNTER_PULSE_FRAMES
      ? interpolate(pulseLocalFrame, [0, 4, COUNTER_PULSE_FRAMES], [1.0, 1.2, 1.0], {
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.quad),
        })
      : 1.0;

  return (
    <div
      style={{
        position: 'absolute',
        right: 140,
        top: 60,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'flex-end',
      }}
    >
      <span
        style={{
          fontFamily: "'Inter', sans-serif",
          fontSize: 12,
          fontWeight: 600,
          color: COUNTER_LABEL_COLOR,
          letterSpacing: '0.1em',
          marginBottom: 4,
        }}
      >
        WALLS:
      </span>
      <span
        style={{
          fontFamily: "'Inter', sans-serif",
          fontSize: 24,
          fontWeight: 700,
          color: COUNTER_NUMBER_COLOR,
          transform: `scale(${scale})`,
          display: 'inline-block',
          transformOrigin: 'center',
        }}
      >
        {currentCount}
      </span>
    </div>
  );
};
