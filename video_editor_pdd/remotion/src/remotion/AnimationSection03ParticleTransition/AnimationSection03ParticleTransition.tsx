import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';
import { CANVAS, TIMING } from './constants';
import { BackgroundMorph } from './BackgroundMorph';
import { ParticleBurst } from './ParticleBurst';
import { CenterFlash } from './CenterFlash';

export const AnimationSection03ParticleTransition: React.FC = () => {
  const frame = useCurrentFrame();

  // Vignette intensifies during the burst phase
  const vignetteIntensity = interpolate(
    frame,
    [TIMING.gatherStart, TIMING.burstStart, TIMING.burstEnd],
    [0.2, 0.2, 0.5],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill
      style={{
        width: CANVAS.width,
        height: CANVAS.height,
        overflow: 'hidden',
      }}
    >
      {/* Cross-fading background (gradient → red) */}
      <BackgroundMorph />

      {/* Radial vignette overlay */}
      <AbsoluteFill
        style={{
          background: `radial-gradient(ellipse at center, transparent 40%, rgba(0,0,0,${vignetteIntensity}) 100%)`,
        }}
      />

      {/* Particle burst system with trails */}
      <ParticleBurst />

      {/* Center flash pulse */}
      <CenterFlash />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection03ParticleTransitionProps = {};

export default AnimationSection03ParticleTransition;
