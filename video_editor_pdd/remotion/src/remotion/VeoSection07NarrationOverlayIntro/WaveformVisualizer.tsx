import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, WAVEFORM } from './constants';

export const WaveformVisualizer: React.FC = () => {
  const frame = useCurrentFrame();

  // Ramp up from frame 8 onward
  const intensity = interpolate(
    frame,
    [ANIMATION.waveformStart, ANIMATION.waveformStart + 4],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const totalWidth =
    WAVEFORM.barCount * WAVEFORM.barWidth +
    (WAVEFORM.barCount - 1) * WAVEFORM.barGap;

  const bars: { x: number; height: number }[] = [];

  // Each bar oscillates at a different phase to simulate audio waveform
  const phaseOffsets = [0, 1.2, 0.5, 1.8, 0.9];

  for (let i = 0; i < WAVEFORM.barCount; i++) {
    const phase = phaseOffsets[i];

    // easeInOutSine oscillation per bar
    const t = (Math.sin(frame * 0.3 + phase * Math.PI * 2) + 1) / 2;
    const easedT = 0.5 - 0.5 * Math.cos(Math.PI * t);

    const height =
      WAVEFORM.minHeight +
      (WAVEFORM.maxHeight - WAVEFORM.minHeight) * easedT * intensity;

    bars.push({
      x: i * (WAVEFORM.barWidth + WAVEFORM.barGap),
      height,
    });
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: WAVEFORM.left,
        bottom: WAVEFORM.bottom,
        width: totalWidth,
        height: WAVEFORM.maxHeight,
        display: 'flex',
        alignItems: 'flex-end',
        gap: WAVEFORM.barGap,
      }}
    >
      {bars.map((bar, i) => (
        <div
          key={i}
          style={{
            width: WAVEFORM.barWidth,
            height: bar.height,
            borderRadius: WAVEFORM.barWidth / 2,
            backgroundColor: COLORS.gold,
          }}
        />
      ))}
    </div>
  );
};
