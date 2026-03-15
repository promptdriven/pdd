import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { DIVIDER, CANVAS, TIMING } from './constants';

export const GlowingDivider: React.FC = () => {
  const frame = useCurrentFrame();

  // Divider drifts from startX to endX during frames 6-18, easeInOutSine
  const dividerX = interpolate(
    frame,
    [TIMING.driftStart, TIMING.driftEnd],
    [DIVIDER.startX, DIVIDER.endX],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    },
  );

  // Glow opacity pulses between 0.25 and 0.35 using sin(t) during drift phase
  const glowPhase = interpolate(
    frame,
    [TIMING.driftStart, TIMING.driftEnd],
    [0, Math.PI * 2],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );
  const glowOpacity = 0.3 + 0.05 * Math.sin(glowPhase);

  return (
    <>
      {/* Glow band: soft blur behind divider */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: dividerX - DIVIDER.glowWidth / 2,
          width: DIVIDER.glowWidth,
          height: CANVAS.height,
          backgroundColor: DIVIDER.color,
          opacity: glowOpacity,
          filter: `blur(${DIVIDER.glowBlur}px)`,
        }}
      />
      {/* Divider line: crisp cyan line */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: dividerX - DIVIDER.width / 2,
          width: DIVIDER.width,
          height: CANVAS.height,
          backgroundColor: DIVIDER.color,
        }}
      />
    </>
  );
};
