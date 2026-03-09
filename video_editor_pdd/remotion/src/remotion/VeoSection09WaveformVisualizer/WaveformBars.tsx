import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { WAVEFORM, POSITIONS, ANIMATION, COLORS } from './constants';

/**
 * Generates a pseudo-random max height for each bar index.
 * Uses a deterministic seed so heights are consistent across renders.
 */
const getBarMaxHeight = (index: number): number => {
  const seed = Math.sin(index * 127.1 + 311.7) * 43758.5453;
  const normalized = seed - Math.floor(seed); // 0..1
  return WAVEFORM.minHeight + normalized * (WAVEFORM.maxHeight - WAVEFORM.minHeight);
};

/**
 * Interpolates color between amber (#F59E0B) and emerald (#34D399) based on t (0..1).
 */
const lerpColor = (t: number): string => {
  // Amber: rgb(245, 158, 11)
  // Emerald: rgb(52, 211, 153)
  const r = Math.round(245 + (52 - 245) * t);
  const g = Math.round(158 + (211 - 158) * t);
  const b = Math.round(11 + (153 - 11) * t);
  return `rgb(${r}, ${g}, ${b})`;
};

export const WaveformBars: React.FC = () => {
  const frame = useCurrentFrame();

  const bars = Array.from({ length: WAVEFORM.barCount }, (_, i) => {
    const maxH = getBarMaxHeight(i);
    const colorT = i / (WAVEFORM.barCount - 1);
    const color = lerpColor(colorT);

    // Phase 1: Grow in (staggered left-to-right)
    const growDelay = i * ANIMATION.staggerPerBar;
    const growProgress = interpolate(
      frame,
      [ANIMATION.growStart + growDelay, ANIMATION.growEnd + growDelay],
      [0, 1],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.quad),
      }
    );

    // Phase 3: Shrink out (staggered right-to-left)
    const shrinkDelay = (WAVEFORM.barCount - 1 - i) * ANIMATION.staggerPerBar;
    const shrinkProgress = interpolate(
      frame,
      [ANIMATION.shrinkStart + shrinkDelay, ANIMATION.shrinkEnd + shrinkDelay],
      [1, 0],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.in(Easing.quad),
      }
    );

    // Phase 2: Oscillation (sine wave offset by bar index)
    let oscillationFactor = 1;
    if (frame >= ANIMATION.oscillateStart && frame <= ANIMATION.oscillateEnd) {
      const oscillationPhase = (frame - ANIMATION.oscillateStart) * 0.15 + i * 0.4;
      const sineValue = Math.sin(oscillationPhase); // -1..1
      const normalized = (sineValue + 1) / 2; // 0..1
      oscillationFactor =
        ANIMATION.oscillationMinFactor +
        normalized * (ANIMATION.oscillationMaxFactor - ANIMATION.oscillationMinFactor);
    }

    // Combine: grow/shrink envelope * oscillation
    const envelope = Math.min(growProgress, shrinkProgress);
    const barHeight = maxH * oscillationFactor * envelope;

    const x = POSITIONS.waveformStartX + i * (WAVEFORM.barWidth + WAVEFORM.barGap);
    const y = WAVEFORM.baselineY - barHeight;

    return (
      <div
        key={i}
        style={{
          position: 'absolute',
          left: x,
          top: y,
          width: WAVEFORM.barWidth,
          height: Math.max(barHeight, 0),
          backgroundColor: color,
          borderRadius: `${WAVEFORM.borderRadius}px ${WAVEFORM.borderRadius}px 0 0`,
        }}
      />
    );
  });

  return <>{bars}</>;
};
