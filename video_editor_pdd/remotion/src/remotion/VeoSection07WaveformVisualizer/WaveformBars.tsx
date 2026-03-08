import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  DIMENSIONS,
  ANIMATION,
  AMPLITUDE_KEYFRAMES,
  COLORS,
} from './constants';

/** Returns an amplitude value for a given bar index at a given oscillation progress (0-1). */
function getAmplitude(barIndex: number, progress: number): number {
  const keyframeCount = AMPLITUDE_KEYFRAMES.length;
  // Shift the wave pattern over time so bars oscillate
  const phase = progress * keyframeCount * 2; // cycles through the pattern twice
  const idx = (barIndex + phase) % keyframeCount;
  const low = Math.floor(idx) % keyframeCount;
  const high = (low + 1) % keyframeCount;
  const t = idx - Math.floor(idx);
  // Smooth interpolation between keyframe values
  const smoothT = 0.5 - 0.5 * Math.cos(t * Math.PI); // easeInOutSine
  return AMPLITUDE_KEYFRAMES[low] * (1 - smoothT) + AMPLITUDE_KEYFRAMES[high] * smoothT;
}

export const WaveformBars: React.FC = () => {
  const frame = useCurrentFrame();

  const totalWidth =
    DIMENSIONS.barCount * DIMENSIONS.barWidth +
    (DIMENSIONS.barCount - 1) * (DIMENSIONS.barSpacing - DIMENSIONS.barWidth);
  const startX = -totalWidth / 2;

  // Fade out shrink
  const fadeOutScale = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.in(Easing.cubic) },
  );

  // Oscillation progress (0-1 over the oscillation window)
  const oscProgress = interpolate(
    frame,
    [ANIMATION.oscillationStart, ANIMATION.oscillationEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: '50%',
        transform: 'translate(-50%, -50%)',
        width: totalWidth,
        height: DIMENSIONS.containerHeight,
        display: 'flex',
        alignItems: 'center',
      }}
    >
      {Array.from({ length: DIMENSIONS.barCount }).map((_, i) => {
        // Stagger grow: group bars into groups of barsGroupSize
        const groupIndex = Math.floor(i / ANIMATION.barsGroupSize);
        const barGrowStart = ANIMATION.barsGrowStart + groupIndex * ANIMATION.barsStaggerDelay;
        const barGrowEnd = barGrowStart + (ANIMATION.barsGrowEnd - ANIMATION.barsGrowStart);

        const growScale = interpolate(
          frame,
          [barGrowStart, barGrowEnd],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.back(1.4)),
          },
        );

        // Get oscillating amplitude
        const amplitude = frame >= ANIMATION.oscillationStart
          ? getAmplitude(i, oscProgress)
          : AMPLITUDE_KEYFRAMES[i % AMPLITUDE_KEYFRAMES.length];

        const barHeight =
          DIMENSIONS.barMinHeight +
          (DIMENSIONS.barMaxHeight - DIMENSIONS.barMinHeight) * amplitude;

        const finalHeight = barHeight * growScale * fadeOutScale;

        // Color: interpolate between base gold and peak gold based on amplitude
        const peakFactor = amplitude;
        const x = startX + i * DIMENSIONS.barSpacing;

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: x + totalWidth / 2,
              top: '50%',
              transform: `translateY(-50%)`,
              width: DIMENSIONS.barWidth,
              height: Math.max(finalHeight, 2),
              borderRadius: DIMENSIONS.barBorderRadius,
              background: `linear-gradient(to top, ${COLORS.barBase}, ${peakFactor > 0.6 ? COLORS.barPeak : COLORS.barBase})`,
              opacity: fadeOutScale,
            }}
          />
        );
      })}
    </div>
  );
};
