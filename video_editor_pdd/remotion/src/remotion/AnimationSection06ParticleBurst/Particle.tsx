import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, TIMING, type ParticleData } from './constants';
import { resolveParticleOpacity } from './motion';

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

  const opacity = resolveParticleOpacity({ frame, currentDistance, maxDistance });

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
