import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COUNTER_X,
  COUNTER_Y,
  COUNTER_LABEL_COLOR,
  COUNTER_NUMBER_COLOR,
  START_WALL_COUNT,
  CYCLE_FRAMES,
  WALL_CYCLES,
  COUNTER_PULSE_DURATION,
} from './constants';

export const WallCounter: React.FC = () => {
  const frame = useCurrentFrame();

  // Calculate current wall count based on completed cycles
  let count = START_WALL_COUNT;
  let lastIncrementFrame = -100;

  for (let i = 0; i < WALL_CYCLES.length; i++) {
    const incrementFrame = i * CYCLE_FRAMES + 8; // increment when wall starts appearing
    if (frame >= incrementFrame) {
      count = START_WALL_COUNT + i + 1;
      lastIncrementFrame = incrementFrame;
    }
  }

  // Scale pulse on increment
  const timeSinceIncrement = frame - lastIncrementFrame;
  const pulseScale =
    timeSinceIncrement >= 0 && timeSinceIncrement < COUNTER_PULSE_DURATION
      ? interpolate(timeSinceIncrement, [0, 4, COUNTER_PULSE_DURATION], [1.0, 1.2, 1.0], {
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.quad),
        })
      : 1.0;

  return (
    <div
      style={{
        position: 'absolute',
        left: COUNTER_X - 60,
        top: COUNTER_Y,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        width: 80,
      }}
    >
      {/* Label */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 12,
          fontWeight: 600,
          color: COUNTER_LABEL_COLOR,
          letterSpacing: '0.08em',
          marginBottom: 4,
        }}
      >
        WALLS:
      </div>
      {/* Count */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 24,
          fontWeight: 700,
          color: COUNTER_NUMBER_COLOR,
          transform: `scale(${pulseScale})`,
          textAlign: 'center',
        }}
      >
        {count}
      </div>
    </div>
  );
};
