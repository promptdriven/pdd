import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { TIMING, CANVAS, PARTICLES, type ParticleData } from './constants';

interface ParticleProps {
  particle: ParticleData;
}

export const Particle: React.FC<ParticleProps> = ({ particle }) => {
  const frame = useCurrentFrame();

  const { angle, speed, size, color, shape, rotationSpeed } = particle;

  // Particles only begin moving at particleStartFrame
  const particleFrame = frame - TIMING.particleStartFrame;
  if (particleFrame < 0) return null;

  // Linear travel: constant velocity, physics-based
  // speed is in px/sec, convert to px/frame
  const speedPerFrame = speed / TIMING.fps;
  const distance = particleFrame * speedPerFrame;

  // Position based on angle and distance from center
  const x = CANVAS.centerX + Math.cos(angle) * distance;
  const y = CANVAS.centerY + Math.sin(angle) * distance;

  // Opacity: full until fadeStart, then easeInCubic fade to 0 by fadeEnd
  const opacity = interpolate(
    frame,
    [TIMING.particleFadeStart, TIMING.particleFadeEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.cubic),
    }
  );

  // Linear rotation: constant angular velocity
  const rotation = particleFrame * rotationSpeed;

  // Don't render if fully faded
  if (opacity <= 0) return null;

  // Don't render if off-screen
  if (
    x < -size ||
    x > CANVAS.width + size ||
    y < -size ||
    y > CANVAS.height + size
  ) {
    return null;
  }

  const borderRadius =
    shape === 'circle' ? '50%' : PARTICLES.greenBorderRadius;

  return (
    <div
      style={{
        position: 'absolute',
        left: x - size / 2,
        top: y - size / 2,
        width: size,
        height: size,
        backgroundColor: color,
        opacity,
        transform: `rotate(${rotation}deg)`,
        borderRadius,
      }}
    />
  );
};
