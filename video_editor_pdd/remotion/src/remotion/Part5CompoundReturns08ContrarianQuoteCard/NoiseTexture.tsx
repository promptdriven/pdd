import React, { useMemo } from 'react';
import { AbsoluteFill, useCurrentFrame, Easing, interpolate } from 'remotion';
import { COLORS, TIMING } from './constants';

/**
 * Subtle noise texture overlay using CSS radial-gradient pattern.
 * Fades in with the background.
 */
export const NoiseTexture: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [TIMING.bgFadeStart, TIMING.bgFadeStart + TIMING.bgFadeDuration],
    [0, 0.02],
    {
      easing: Easing.out(Easing.quad),
      extrapolateRight: 'clamp',
    }
  );

  // Generate a pseudo-noise pattern using multiple layered gradients
  const noiseStyle = useMemo(
    () => ({
      backgroundImage: `
        radial-gradient(circle at 20% 30%, ${COLORS.noiseTexture} 0.5px, transparent 0.5px),
        radial-gradient(circle at 80% 60%, ${COLORS.noiseTexture} 0.5px, transparent 0.5px),
        radial-gradient(circle at 40% 80%, ${COLORS.noiseTexture} 0.3px, transparent 0.3px),
        radial-gradient(circle at 60% 20%, ${COLORS.noiseTexture} 0.4px, transparent 0.4px),
        radial-gradient(circle at 10% 70%, ${COLORS.noiseTexture} 0.3px, transparent 0.3px),
        radial-gradient(circle at 90% 40%, ${COLORS.noiseTexture} 0.4px, transparent 0.4px)
      `,
      backgroundSize: '80px 80px, 120px 120px, 60px 60px, 100px 100px, 90px 90px, 70px 70px',
    }),
    []
  );

  return (
    <AbsoluteFill
      style={{
        ...noiseStyle,
        opacity,
        pointerEvents: 'none',
      }}
    />
  );
};

export default NoiseTexture;
