import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TIMING } from './constants';

export const BackgroundMorph: React.FC = () => {
  const frame = useCurrentFrame();

  // Cross-fade progress from gradient to solid red
  const crossfade = interpolate(
    frame,
    [TIMING.burstStart, TIMING.burstEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  return (
    <>
      {/* Navy gradient background (fading out) */}
      <AbsoluteFill
        style={{
          background: `linear-gradient(180deg, ${COLORS.gradientTop} 0%, ${COLORS.gradientBottom} 100%)`,
          opacity: 1 - crossfade,
        }}
      />
      {/* Solid red background (fading in) */}
      <AbsoluteFill
        style={{
          backgroundColor: COLORS.targetBackground,
          opacity: crossfade,
        }}
      />
    </>
  );
};
