import React from 'react';
import { useCurrentFrame } from 'remotion';
import { COLORS, ANIMATION } from './constants';

const BAR_COUNT = 32;
const BAR_WIDTH = 3;
const BAR_GAP = 2;
const MAX_HEIGHT = 60;
const VISUAL_WIDTH = BAR_COUNT * (BAR_WIDTH + BAR_GAP);
const VISUAL_HEIGHT = MAX_HEIGHT + 10;

export const WaveformVisual: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <div
      style={{
        width: VISUAL_WIDTH,
        height: VISUAL_HEIGHT,
        display: 'flex',
        alignItems: 'flex-end',
        gap: BAR_GAP,
      }}
    >
      {Array.from({ length: BAR_COUNT }).map((_, i) => {
        // Animated wave pattern using sin with offset per bar
        const phase = frame * ANIMATION.waveformSpeed + i * 0.4;
        const sin1 = Math.sin(phase) * 0.5 + 0.5;
        const sin2 = Math.sin(phase * 0.7 + 1.2) * 0.3 + 0.3;
        const height = Math.max(4, (sin1 + sin2) * MAX_HEIGHT * 0.6);

        // Color varies across the waveform
        const t = i / BAR_COUNT;
        const r = Math.round(59 + t * (6 - 59));
        const g = Math.round(130 + t * (182 - 130));
        const b = Math.round(246 + t * (212 - 246));
        const barColor = `rgb(${r}, ${g}, ${b})`;

        return (
          <div
            key={i}
            style={{
              width: BAR_WIDTH,
              height,
              borderRadius: 1.5,
              backgroundColor: barColor,
              opacity: 0.8,
              boxShadow: `0 0 4px ${COLORS.accentBlue}33`,
            }}
          />
        );
      })}
    </div>
  );
};
