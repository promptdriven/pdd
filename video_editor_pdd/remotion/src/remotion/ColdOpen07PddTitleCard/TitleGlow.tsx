import React from 'react';
import { Easing, interpolate, useCurrentFrame } from 'remotion';
import { COLORS, GLOW, TIMING } from './constants';

/**
 * Renders a glow layer behind the title text.
 * Pulses gently between GLOW.OPACITY_MIN and GLOW.OPACITY_MAX
 * starting from frame TIMING.HOLD_START on a repeating cycle.
 */
export const TitleGlow: React.FC<{
  y: number;
  text: string;
  startFrame: number;
}> = ({ y, text, startFrame }) => {
  const frame = useCurrentFrame();

  // Only visible after the title line has started fading in
  if (frame < startFrame) return null;

  const localFrame = frame - startFrame;

  // Fade-in opacity for the glow matches the title fade-in (25 frames)
  const fadeIn = interpolate(localFrame, [0, 25], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Pulse: once we're in the hold phase, pulse the glow
  let pulseOpacity = GLOW.OPACITY_MIN;
  if (frame >= TIMING.HOLD_START) {
    const pulseFrame = (frame - TIMING.HOLD_START) % GLOW.PULSE_CYCLE;
    // Use a sine-based easeInOut for smooth pulsing
    // 0 → peak at half cycle → back to 0
    const halfCycle = GLOW.PULSE_CYCLE / 2;
    const pulseProgress =
      pulseFrame < halfCycle
        ? interpolate(pulseFrame, [0, halfCycle], [0, 1], {
            easing: Easing.inOut(Easing.sin),
          })
        : interpolate(pulseFrame, [halfCycle, GLOW.PULSE_CYCLE], [1, 0], {
            easing: Easing.inOut(Easing.sin),
          });

    pulseOpacity = interpolate(
      pulseProgress,
      [0, 1],
      [GLOW.OPACITY_MIN, GLOW.OPACITY_MAX]
    );
  }

  const glowOpacity = fadeIn * pulseOpacity;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'flex-start',
        pointerEvents: 'none',
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: y - 40,
          fontFamily: 'Inter, sans-serif',
          fontSize: 64,
          fontWeight: 700,
          color: COLORS.TITLE,
          opacity: glowOpacity,
          filter: `blur(${GLOW.BLUR}px)`,
          textAlign: 'center',
          whiteSpace: 'nowrap',
          userSelect: 'none',
        }}
      >
        {text}
      </div>
    </div>
  );
};
