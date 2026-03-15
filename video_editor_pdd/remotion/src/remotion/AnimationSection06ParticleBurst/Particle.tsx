import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, PARTICLES, TIMING, type ParticleData } from './constants';

interface ParticleProps {
  particle: ParticleData;
}

/**
 * Individual particle that radiates outward from center along a straight-line
 * trajectory with easeOutCubic deceleration.
 * Fading begins at 60% of travel distance using easeInQuad.
 */
export const Particle: React.FC<ParticleProps> = ({ particle }) => {
  const frame = useCurrentFrame();

  const { angle, maxDistance, radius, color } = particle;

  // Particle movement: frames particleStart to particleMoveEnd
  const moveDuration = TIMING.particleMoveEnd - TIMING.particleStart;
  const particleFrame = Math.max(0, frame - TIMING.particleStart);

  // Not visible before particles start
  if (frame < TIMING.particleStart) return null;

  // Radial progress with easeOutCubic deceleration
  const progress = interpolate(
    particleFrame,
    [0, moveDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const currentDistance = maxDistance * progress;
  const x = CANVAS.centerX + Math.cos(angle) * currentDistance;
  const y = CANVAS.centerY + Math.sin(angle) * currentDistance;

  // Opacity: full until 60% of travel, then fade to 0 with easeInQuad
  const fadeStartDistance = maxDistance * PARTICLES.fadeStartRatio;
  let opacity: number;

  if (currentDistance <= fadeStartDistance) {
    opacity = 1;
  } else {
    const fadeProgress = (currentDistance - fadeStartDistance) / (maxDistance - fadeStartDistance);
    opacity = interpolate(
      fadeProgress,
      [0, 1],
      [1, 0],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.in(Easing.quad),
      },
    );
  }

  // After move phase, any remaining particles continue fading (frames 22-30)
  if (frame > TIMING.particleMoveEnd) {
    const tailFade = interpolate(
      frame,
      [TIMING.particleMoveEnd, TIMING.totalEnd],
      [opacity, 0],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.in(Easing.quad),
      },
    );
    opacity = tailFade;
  }

  if (opacity <= 0) return null;

  // Skip off-screen particles
  const diameter = radius * 2;
  if (
    x < -diameter ||
    x > CANVAS.width + diameter ||
    y < -diameter ||
    y > CANVAS.height + diameter
  ) {
    return null;
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: x - radius,
        top: y - radius,
        width: diameter,
        height: diameter,
        borderRadius: '50%',
        backgroundColor: color,
        opacity,
      }}
    />
  );
};
