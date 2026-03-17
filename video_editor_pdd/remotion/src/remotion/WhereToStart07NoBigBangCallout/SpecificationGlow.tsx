import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, TIMING } from './constants';

/**
 * The "from code to specification." line with colored keywords and glow effect.
 * "code" renders in neutral gray, "specification" in glowing blue.
 */
export const SpecificationLine: React.FC<{ opacity: number }> = ({ opacity }) => {
  const frame = useCurrentFrame();

  // Glow bloom on "specification" — ramps up from frame 100 to 112
  const glowBloomStart = TIMING.LINE3_START + TIMING.LINE3B_OFFSET;
  const glowBloomProgress = interpolate(
    frame,
    [glowBloomStart, glowBloomStart + 12],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Final pulse on "specification" glow (frame 130-150)
  const pulseProgress = interpolate(
    frame,
    [TIMING.PULSE_START, TIMING.PULSE_START + TIMING.PULSE_DURATION],
    [0, Math.PI * 2],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const pulseActive = frame >= TIMING.PULSE_START;
  const pulseFactor = pulseActive ? Math.sin(pulseProgress) : 0;

  const baseGlowOpacity = TYPOGRAPHY.SPEC_GLOW_OPACITY * glowBloomProgress;
  const glowOpacity = interpolate(
    pulseFactor,
    [-1, 0, 1],
    [baseGlowOpacity, baseGlowOpacity, 0.25]
  );
  const glowBlur = TYPOGRAPHY.SPEC_GLOW_BLUR * glowBloomProgress;

  return (
    <div
      style={{
        opacity,
        fontFamily: TYPOGRAPHY.FONT_FAMILY,
        fontSize: TYPOGRAPHY.LINE3B.size,
        fontWeight: TYPOGRAPHY.LINE3B.weight,
        textAlign: 'center',
        lineHeight: 1.4,
      }}
    >
      <span style={{ color: COLORS.TEXT_PRIMARY, opacity: 0.4 }}>from </span>
      <span
        style={{
          color: COLORS.TEXT_GRAY,
          opacity: TYPOGRAPHY.CODE_OPACITY,
          fontWeight: 600,
        }}
      >
        code
      </span>
      <span style={{ color: COLORS.TEXT_PRIMARY, opacity: 0.4 }}> to </span>
      <span
        style={{
          color: COLORS.TEXT_BLUE,
          opacity: TYPOGRAPHY.SPEC_OPACITY,
          fontWeight: 600,
          textShadow: `0 0 ${glowBlur}px rgba(74, 144, 217, ${glowOpacity})`,
        }}
      >
        specification
      </span>
      <span style={{ color: COLORS.TEXT_PRIMARY, opacity: 0.4 }}>.</span>
    </div>
  );
};
