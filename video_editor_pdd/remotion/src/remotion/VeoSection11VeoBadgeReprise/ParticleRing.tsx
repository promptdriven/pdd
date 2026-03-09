import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, POSITIONS, DIMENSIONS, ANIMATION } from './constants';

const PARTICLES = Array.from({ length: DIMENSIONS.particleCount }, (_, i) => ({
  index: i,
  angle: (i / DIMENSIONS.particleCount) * Math.PI * 2,
  size: DIMENSIONS.particleMinSize + (i % 3) * ((DIMENSIONS.particleMaxSize - DIMENSIONS.particleMinSize) / 2),
  oscillationPhase: (i / DIMENSIONS.particleCount) * Math.PI * 2,
}));

export const ParticleRing: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in: frames 30-45
  const opacityIn = interpolate(
    frame,
    [ANIMATION.particleStart, ANIMATION.particleFadeEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Fade out: frames 75-90
  const opacityOut = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(2)),
    },
  );

  const opacity = Math.min(opacityIn, opacityOut);

  // Orbit rotation: linear, full rotation over 90 frames
  const orbitProgress = frame >= ANIMATION.particleStart
    ? (frame - ANIMATION.particleStart) / ANIMATION.particleOrbitFrames
    : 0;
  const orbitAngle = orbitProgress * Math.PI * 2;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        opacity,
      }}
    >
      {PARTICLES.map((particle) => {
        const currentAngle = particle.angle + orbitAngle;

        // Radial oscillation
        const oscillation = Math.sin(
          particle.oscillationPhase + frame * 0.1,
        ) * ANIMATION.particleOscillationAmplitude;
        const currentRadius = DIMENSIONS.particleRadius + oscillation;

        const x = POSITIONS.center + Math.cos(currentAngle) * currentRadius;
        const y = POSITIONS.wordmarkY + Math.sin(currentAngle) * currentRadius;

        return (
          <div
            key={particle.index}
            style={{
              position: 'absolute',
              left: x - particle.size / 2,
              top: y - particle.size / 2,
              width: particle.size,
              height: particle.size,
              borderRadius: '50%',
              backgroundColor: COLORS.particleColor,
              opacity: COLORS.particleOpacity,
            }}
          />
        );
      })}
    </div>
  );
};
