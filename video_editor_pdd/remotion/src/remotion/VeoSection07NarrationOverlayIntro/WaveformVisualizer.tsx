import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { WAVEFORM, COLORS, ANIMATION } from './constants';

/**
 * Attempt a simple seeded pseudo-random number from an integer seed.
 * Returns a value between 0 and 1.
 */
const seededRandom = (seed: number): number => {
  const x = Math.sin(seed * 12.9898 + seed * 78.233) * 43758.5453;
  return x - Math.floor(x);
};

export const WaveformVisualizer: React.FC = () => {
  const frame = useCurrentFrame();

  // Ramp up from 0 to full intensity between waveformStart and waveformRampEnd
  const rampUp = interpolate(
    frame,
    [ANIMATION.waveformStart, ANIMATION.waveformRampEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Tail off: reduce to minimal heights at the end
  const tailOff = interpolate(
    frame,
    [ANIMATION.waveformTailStart, ANIMATION.waveformTailEnd],
    [1, 0.1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  const intensity = rampUp * tailOff;

  const totalBarSpace = WAVEFORM.xEnd - WAVEFORM.xStart;
  const barPitch = totalBarSpace / WAVEFORM.barCount;

  const bars: { x: number; height: number; phaseOffset: number }[] = [];
  for (let i = 0; i < WAVEFORM.barCount; i++) {
    const phaseOffset = seededRandom(i * 7 + 3) * Math.PI * 2;

    // Oscillate bar height with sine wave, phase-shifted per bar
    const oscillation =
      0.5 +
      0.5 *
        Math.sin(
          (frame * 0.3 + phaseOffset) *
            (0.8 + seededRandom(i * 13 + 5) * 0.4),
        );

    const baseHeight =
      WAVEFORM.minHeight +
      (WAVEFORM.maxHeight - WAVEFORM.minHeight) * seededRandom(i * 17 + 11);

    const animatedHeight =
      WAVEFORM.minHeight +
      (baseHeight - WAVEFORM.minHeight) * oscillation * intensity;

    bars.push({
      x: WAVEFORM.xStart + i * barPitch,
      height: animatedHeight,
      phaseOffset,
    });
  }

  return (
    <>
      {bars.map((bar, i) => {
        const barTop = WAVEFORM.baselineY - bar.height;
        return (
          <React.Fragment key={i}>
            {/* Main bar */}
            <div
              style={{
                position: 'absolute',
                left: bar.x,
                top: barTop,
                width: WAVEFORM.barWidth,
                height: bar.height,
                borderRadius: WAVEFORM.barWidth / 2,
                background: `linear-gradient(to top, ${COLORS.waveformBottom}, ${COLORS.waveformTop})`,
                opacity: COLORS.waveformOpacity,
              }}
            />
            {/* Reflection below baseline */}
            <div
              style={{
                position: 'absolute',
                left: bar.x,
                top: WAVEFORM.baselineY,
                width: WAVEFORM.barWidth,
                height: bar.height * 0.5,
                borderRadius: WAVEFORM.barWidth / 2,
                background: `linear-gradient(to bottom, ${COLORS.waveformBottom}, transparent)`,
                opacity: COLORS.waveformReflectionOpacity,
              }}
            />
          </React.Fragment>
        );
      })}
    </>
  );
};
