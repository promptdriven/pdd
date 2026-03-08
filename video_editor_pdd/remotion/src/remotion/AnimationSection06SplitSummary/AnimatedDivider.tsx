import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, DIVIDER, TIMING } from './constants';

/**
 * Animated vertical divider that slides from startX to endX
 * with a glowing blue effect that pulses near the end.
 */
export const AnimatedDivider: React.FC = () => {
  const frame = useCurrentFrame();

  // Slide from left-of-center to right-of-center
  const x = interpolate(
    frame,
    [TIMING.dividerSlideStart, TIMING.dividerSlideEnd],
    [DIVIDER.startX, DIVIDER.endX],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Glow pulse: 0.4 -> 0.7 -> 0.4 over frames 60-90
  const glowOpacity = (() => {
    if (frame < TIMING.glowPulseStart) return 0.4;
    if (frame <= TIMING.glowPulseMid) {
      return interpolate(
        frame,
        [TIMING.glowPulseStart, TIMING.glowPulseMid],
        [0.4, 0.7],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.sin),
        }
      );
    }
    return interpolate(
      frame,
      [TIMING.glowPulseMid, TIMING.glowPulseEnd],
      [0.7, 0.4],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      }
    );
  })();

  return (
    <div
      style={{
        position: 'absolute',
        left: x - DIVIDER.width / 2,
        top: 0,
        width: DIVIDER.width,
        height: CANVAS.height,
        backgroundColor: COLORS.divider,
        boxShadow: `0 0 ${DIVIDER.glowBlur}px rgba(59, 130, 246, ${glowOpacity})`,
        zIndex: 10,
      }}
    />
  );
};
