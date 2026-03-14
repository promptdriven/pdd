import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, DIMENSIONS } from './constants';

/**
 * Seeded pseudo-random number from an integer seed.
 * Returns a value between 0 and 1.
 */
const seededRandom = (seed: number): number => {
  const x = Math.sin(seed * 12.9898 + seed * 78.233) * 43758.5453;
  return x - Math.floor(x);
};

export const WaveformVisualizer: React.FC = () => {
  const frame = useCurrentFrame();

  const {
    waveformBarCount,
    waveformBarWidth,
    waveformBarGap,
    waveformMinHeight,
    waveformMaxHeight,
    waveformY,
  } = DIMENSIONS;

  // Total width of waveform: (barWidth + barGap) * barCount - barGap
  const totalWidth =
    (waveformBarWidth + waveformBarGap) * waveformBarCount - waveformBarGap;
  const startX = (1920 - totalWidth) / 2;

  // Frame 10–20: Ramp up intensity from 0→1
  const rampUp = interpolate(
    frame,
    [ANIMATION.waveformStart, ANIMATION.waveformEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const bars: { x: number; height: number }[] = [];
  for (let i = 0; i < waveformBarCount; i++) {
    const phaseOffset = seededRandom(i * 7 + 3) * Math.PI * 2;

    // Traveling wave: phase shifts left-to-right based on bar index
    const travelPhase = (i / waveformBarCount) * Math.PI * 2;

    // Sinusoidal oscillation — continuous pulse
    const oscillation =
      0.5 +
      0.5 * Math.sin(frame * 0.4 + phaseOffset + travelPhase);

    // Base height randomized per bar (deterministic via seed)
    const baseHeight =
      waveformMinHeight +
      (waveformMaxHeight - waveformMinHeight) * seededRandom(i * 17 + 11);

    // Animated height: scales with rampUp intensity
    const animatedHeight =
      waveformMinHeight +
      (baseHeight - waveformMinHeight) * oscillation * rampUp;

    bars.push({
      x: startX + i * (waveformBarWidth + waveformBarGap),
      height: animatedHeight,
    });
  }

  return (
    <>
      {bars.map((bar, i) => (
        <div
          key={i}
          style={{
            position: 'absolute',
            left: bar.x,
            top: waveformY - bar.height / 2,
            width: waveformBarWidth,
            height: bar.height,
            borderRadius: waveformBarWidth / 2,
            backgroundColor: COLORS.waveformBar,
          }}
        />
      ))}
    </>
  );
};
