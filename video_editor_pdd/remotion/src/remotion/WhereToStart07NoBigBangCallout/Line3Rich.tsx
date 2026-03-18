import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TIMING, TYPOGRAPHY } from './constants';

/**
 * Line3Rich renders the two-part third line:
 *   "A gradual migration of where value lives —"
 *   "from code to specification."
 * with colored highlights and glow effects.
 */
export const Line3Rich: React.FC = () => {
  const frame = useCurrentFrame();

  // First part fade
  const part1Opacity = interpolate(
    frame,
    [TIMING.LINE3_START, TIMING.LINE3_START + TIMING.LINE3_DURATION],
    [0, 0.4],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Second part fade (starts 10 frames after line3)
  const part2Opacity = interpolate(
    frame,
    [TIMING.LINE3B_START, TIMING.LINE3B_START + TIMING.LINE3B_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // "specification" glow bloom
  const glowBloom = interpolate(
    frame,
    [TIMING.LINE3B_START + 5, TIMING.LINE3B_START + 17],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Final pulse on "specification" glow (frame 130-150)
  const pulsePhase = interpolate(
    frame,
    [TIMING.PULSE_START, TIMING.PULSE_START + TIMING.PULSE_DURATION],
    [0, Math.PI * 2],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    },
  );

  const pulseActive = frame >= TIMING.PULSE_START;
  const pulseMultiplier = pulseActive
    ? 1 + 0.4 * Math.sin(pulsePhase)
    : 1;

  const specGlowOpacity = 0.15 * glowBloom * pulseMultiplier;
  const specGlowBlur = 8 * glowBloom * pulseMultiplier;

  const baseStyle: React.CSSProperties = {
    fontFamily: TYPOGRAPHY.FONT_FAMILY,
    fontSize: 18,
    fontWeight: 400,
    lineHeight: 1.4,
  };

  return (
    <>
      {/* First part: "A gradual migration of where value lives —" */}
      <div
        style={{
          position: 'absolute',
          top: 520,
          left: 0,
          width: 1920,
          display: 'flex',
          justifyContent: 'center',
          opacity: part1Opacity,
        }}
      >
        <span style={{ ...baseStyle, color: COLORS.TEXT_PRIMARY }}>
          A gradual migration of where value lives —
        </span>
      </div>

      {/* Second part: "from code to specification." */}
      <div
        style={{
          position: 'absolute',
          top: 555,
          left: 0,
          width: 1920,
          display: 'flex',
          justifyContent: 'center',
          opacity: part2Opacity,
        }}
      >
        <span style={baseStyle}>
          <span style={{ color: COLORS.TEXT_PRIMARY, opacity: 0.4 }}>
            from{' '}
          </span>
          <span style={{ color: COLORS.NEUTRAL_GRAY, opacity: 0.5 }}>
            code
          </span>
          <span style={{ color: COLORS.TEXT_PRIMARY, opacity: 0.4 }}>
            {' '}to{' '}
          </span>
          <span
            style={{
              color: COLORS.GLOW_BLUE,
              opacity: 0.7,
              textShadow: `0 0 ${specGlowBlur}px rgba(74, 144, 217, ${specGlowOpacity})`,
            }}
          >
            specification
          </span>
          <span style={{ color: COLORS.TEXT_PRIMARY, opacity: 0.4 }}>.</span>
        </span>
      </div>
    </>
  );
};
