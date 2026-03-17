import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  COUNTER_POSITION,
  TOTAL_MODULES,
  CONVERSION_WAVES,
} from './constants';

const CROSSFADE_DURATION = 8;

export const ModuleCounter: React.FC = () => {
  const frame = useCurrentFrame();

  // Find current and next counter values
  let currentValue = 0;
  let nextValue = 0;
  let transitionFrame = 0;

  for (const wave of CONVERSION_WAVES) {
    if (frame >= wave.startFrame) {
      currentValue = wave.cumulative;
    }
  }

  // Check if we're in a crossfade transition
  let crossfadeProgress = 1; // 1 = fully showing currentValue
  for (let i = 1; i < CONVERSION_WAVES.length; i++) {
    const wave = CONVERSION_WAVES[i];
    if (
      frame >= wave.startFrame &&
      frame < wave.startFrame + CROSSFADE_DURATION
    ) {
      transitionFrame = wave.startFrame;
      nextValue = wave.cumulative;
      const prevValue = CONVERSION_WAVES[i - 1].cumulative;
      crossfadeProgress = interpolate(
        frame,
        [transitionFrame, transitionFrame + CROSSFADE_DURATION],
        [0, 1],
        {
          easing: Easing.out(Easing.quad),
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        },
      );
      // We're transitioning from prevValue to nextValue
      currentValue = prevValue;
      break;
    }
  }

  const [cx, cy] = COUNTER_POSITION;

  return (
    <div
      style={{
        position: 'absolute',
        left: cx,
        top: cy,
        fontFamily: 'Inter, sans-serif',
        fontSize: 14,
        whiteSpace: 'nowrap',
      }}
    >
      {crossfadeProgress < 1 ? (
        // During crossfade: show outgoing and incoming
        <div style={{ position: 'relative' }}>
          <span
            style={{
              color: '#4A90D9',
              fontWeight: 700,
              opacity: 0.7 * (1 - crossfadeProgress),
              position: 'absolute',
            }}
          >
            {currentValue}
          </span>
          <span
            style={{
              color: '#4A90D9',
              fontWeight: 700,
              opacity: 0.7 * crossfadeProgress,
            }}
          >
            {nextValue}
          </span>
          <span style={{ color: '#E2E8F0', opacity: 0.5 }}>
            {' '}/ {TOTAL_MODULES} modules
          </span>
        </div>
      ) : (
        <div>
          <span
            style={{
              color: '#4A90D9',
              fontWeight: 700,
              opacity: 0.7,
            }}
          >
            {currentValue}
          </span>
          <span style={{ color: '#E2E8F0', opacity: 0.5 }}>
            {' '}/ {TOTAL_MODULES} modules
          </span>
        </div>
      )}
    </div>
  );
};
