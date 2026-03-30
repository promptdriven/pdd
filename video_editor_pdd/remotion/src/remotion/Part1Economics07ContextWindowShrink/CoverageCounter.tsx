// CoverageCounter.tsx — Displays "Context coverage:" label + animated percentage.
// Color shifts from green → amber → red → dark-red as coverage drops.

import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  GROWTH_STAGES,
  TRANSITION_DURATION,
  COUNTER_X,
  COUNTER_Y,
  COUNTER_LABEL_COLOR,
  COUNTER_LABEL_SIZE,
  COUNTER_VALUE_SIZE,
} from './constants';

/** Lerp between two hex colors. */
function lerpColor(a: string, b: string, t: number): string {
  const parseHex = (hex: string) => {
    const h = hex.replace('#', '');
    return [
      parseInt(h.substring(0, 2), 16),
      parseInt(h.substring(2, 4), 16),
      parseInt(h.substring(4, 6), 16),
    ];
  };
  const ca = parseHex(a);
  const cb = parseHex(b);
  const r = Math.round(ca[0] + (cb[0] - ca[0]) * t);
  const g = Math.round(ca[1] + (cb[1] - ca[1]) * t);
  const bl = Math.round(ca[2] + (cb[2] - ca[2]) * t);
  return `rgb(${r},${g},${bl})`;
}

export const CoverageCounter: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine current and target coverage/color based on frame
  let displayPercent = GROWTH_STAGES[0].coveragePercent;
  let displayColor = GROWTH_STAGES[0].coverageColor;

  for (let i = 1; i < GROWTH_STAGES.length; i++) {
    const stage = GROWTH_STAGES[i];
    const prevStage = GROWTH_STAGES[i - 1];
    const tStart = stage.startFrame;
    const tEnd = tStart + TRANSITION_DURATION;

    if (frame >= tStart) {
      const t = interpolate(frame, [tStart, tEnd], [0, 1], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.quad),
      });
      displayPercent = Math.round(
        prevStage.coveragePercent +
          (stage.coveragePercent - prevStage.coveragePercent) * t,
      );
      // Color transition over 30 frames (slightly faster than number)
      const colorT = interpolate(frame, [tStart, tStart + 30], [0, 1], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.quad),
      });
      displayColor = lerpColor(prevStage.coverageColor, stage.coverageColor, colorT);
    }
  }

  // Fade in with the grid
  const opacity = interpolate(frame, [30, 60], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: COUNTER_X,
        top: COUNTER_Y,
        transform: 'translateX(-50%)',
        textAlign: 'center',
        opacity,
        zIndex: 20,
      }}
    >
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: COUNTER_LABEL_SIZE,
          fontWeight: 400,
          color: COUNTER_LABEL_COLOR,
          marginBottom: 6,
          letterSpacing: '0.02em',
        }}
      >
        Context coverage:
      </div>
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: COUNTER_VALUE_SIZE,
          fontWeight: 700,
          color: displayColor,
          lineHeight: 1,
        }}
      >
        {displayPercent}%
      </div>
    </div>
  );
};

export default CoverageCounter;
