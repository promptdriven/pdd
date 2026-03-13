import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, TIMING, type ParticleData } from './constants';

interface ParticleProps {
  particle: ParticleData;
}

export const Particle: React.FC<ParticleProps> = ({ particle }) => {
  const frame = useCurrentFrame();

  const { angle, distance, radius, color } = particle;

  // Particles begin at frame 2
  const particleFrame = frame - TIMING.particleStart;
  if (particleFrame < 0) return null;

  // Total frames for particle movement
  const moveDuration = TIMING.particleMoveEnd - TIMING.particleStart;

  // Radial progress with easeOutQuart deceleration
  const progress = interpolate(
    particleFrame,
    [0, moveDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(4)),
    }
  );

  const currentDistance = distance * progress;
  const x = CANVAS.centerX + Math.cos(angle) * currentDistance;
  const y = CANVAS.centerY + Math.sin(angle) * currentDistance;

  // Opacity: fade from 1.0 to 0 over particle lifetime, easeInQuad
  const opacity = interpolate(
    particleFrame,
    [0, moveDuration],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
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
