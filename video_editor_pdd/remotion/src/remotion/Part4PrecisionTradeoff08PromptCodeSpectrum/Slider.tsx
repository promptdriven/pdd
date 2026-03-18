import React from 'react';
import { useCurrentFrame, spring, interpolate, Easing } from 'remotion';
import {
  SLIDER_X,
  SLIDER_Y,
  SLIDER_WIDTH,
  SLIDER_HEIGHT,
  BLUE,
  TEXT_PRIMARY,
  TIMING,
} from './constants';

const FPS = 30;

/**
 * The glowing slider/thumb indicator on the spectrum bar.
 * Appears with spring animation at frame 60, then pulses gently.
 */
export const Slider: React.FC = () => {
  const frame = useCurrentFrame();

  // Spring animation for appearance (starts at frame 60)
  const sliderFrame = Math.max(0, frame - TIMING.sliderStart);
  const springScale = spring({
    frame: sliderFrame,
    fps: FPS,
    config: { stiffness: 150, damping: 12 },
  });

  // Gentle pulse after slider is visible (starts after frame ~90)
  const pulseFrame = Math.max(0, frame - (TIMING.sliderStart + 30));
  const pulse = interpolate(
    pulseFrame % TIMING.sliderPulseCycle,
    [0, TIMING.sliderPulseCycle / 2, TIMING.sliderPulseCycle],
    [1, 1.15, 1],
    { extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
  );

  const isVisible = frame >= TIMING.sliderStart;
  if (!isVisible) return null;

  const glowScale = frame >= TIMING.sliderStart + 30 ? pulse : 1;

  return (
    <>
      {/* Glow */}
      <div
        style={{
          position: 'absolute',
          left: SLIDER_X - 8,
          top: SLIDER_Y,
          width: SLIDER_WIDTH + 16,
          height: SLIDER_HEIGHT,
          borderRadius: 4,
          backgroundColor: BLUE,
          filter: 'blur(16px)',
          opacity: 0.3 * springScale,
          transform: `scaleY(${springScale}) scaleX(${glowScale})`,
          transformOrigin: 'center',
        }}
      />

      {/* Slider bar */}
      <div
        style={{
          position: 'absolute',
          left: SLIDER_X - SLIDER_WIDTH / 2,
          top: SLIDER_Y,
          width: SLIDER_WIDTH,
          height: SLIDER_HEIGHT,
          borderRadius: 2,
          backgroundColor: TEXT_PRIMARY,
          opacity: 0.9 * springScale,
          transform: `scaleY(${springScale})`,
          transformOrigin: 'center',
        }}
      />
    </>
  );
};
