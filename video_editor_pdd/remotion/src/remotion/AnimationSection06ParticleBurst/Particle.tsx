import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, TIMING, type ParticleData } from './constants';

interface ParticleProps {
  particle: ParticleData;
}

export const Particle: React.FC<ParticleProps> = ({ particle }) => {
  const frame = useCurrentFrame();

  const { angle, distance, radius, color } = particle;

  // Total frames for particle movement (frames 2-24)
  const moveDuration = TIMING.particleMoveEnd - TIMING.particleStart;
  const particleFrame = Math.max(0, frame - TIMING.particleStart);

  // Radial progress with easeOutCubic deceleration (stationary before frame 2)
  const progress = interpolate(
    particleFrame,
    [0, moveDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const currentDistance = distance * progress;
  const x = CANVAS.centerX + Math.cos(angle) * currentDistance;
  const y = CANVAS.centerY + Math.sin(angle) * currentDistance;

  // Opacity: visible at center before detonation, then linear fade 1→0 during travel
  const fadeDuration = Math.max(1, TIMING.particleFadeEnd - TIMING.particleStart);
  const opacity = frame < TIMING.particleStart
    ? 1
    : interpolate(
        particleFrame,
        [0, fadeDuration],
        [1, 0],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        }
      );

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
