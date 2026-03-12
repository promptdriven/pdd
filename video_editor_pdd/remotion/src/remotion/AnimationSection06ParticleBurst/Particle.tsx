import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { TIMING, CANVAS, type ParticleData } from './constants';

interface ParticleProps {
  particle: ParticleData;
}

export const Particle: React.FC<ParticleProps> = ({ particle }) => {
  const frame = useCurrentFrame();

  const { angle, speed, size, color, shape, rotationSpeed } = particle;

  // Convert speed from px/s to px/frame (at 30fps)
  const speedPerFrame = speed / TIMING.fps;

  // Distance traveled with easeOutQuad deceleration
  const maxDistance = speedPerFrame * TIMING.particleFadeEnd;
  const progress = interpolate(
    frame,
    [0, TIMING.particleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const distance = progress * maxDistance;

  // Position based on angle and distance
  const x = CANVAS.width / 2 + Math.cos(angle) * distance;
  const y = CANVAS.height / 2 + Math.sin(angle) * distance;

  // Opacity: full until fadeStart, then fade to 0
  const opacity = interpolate(
    frame,
    [0, TIMING.particleFadeStart, TIMING.particleFadeEnd],
    [1, 1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Rotation
  const rotation = frame * rotationSpeed;

  // Don't render if invisible or off-screen
  if (opacity <= 0) return null;
  if (x < -size || x > CANVAS.width + size || y < -size || y > CANVAS.height + size) return null;

  const style: React.CSSProperties = {
    position: 'absolute',
    left: x - size / 2,
    top: y - size / 2,
    width: size,
    height: size,
    backgroundColor: color,
    opacity,
    transform: `rotate(${rotation}deg)`,
    borderRadius: shape === 'circle' ? '50%' : 0,
  };

  return <div style={style} />;
};
