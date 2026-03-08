import React from 'react';
import { useCurrentFrame, useVideoConfig, random, interpolate } from 'remotion';
import { PARTICLES, CANVAS } from './constants';

interface Particle {
  id: number;
  startX: number;
  startY: number;
  size: number;
  speed: number;
  xDrift: number;
}

const generateParticles = (count: number): Particle[] => {
  const particles: Particle[] = [];
  for (let i = 0; i < count; i++) {
    particles.push({
      id: i,
      startX: random(`particle-x-${i}`) * CANVAS.width,
      startY: random(`particle-y-${i}`) * CANVAS.height,
      size: random(`particle-size-${i}`) * (PARTICLES.maxSize - PARTICLES.minSize) + PARTICLES.minSize,
      speed: (random(`particle-speed-${i}`) * 0.5 + 0.75) * PARTICLES.speed,
      xDrift: (random(`particle-drift-${i}`) - 0.5) * 100,
    });
  }
  return particles;
};

export const ParticleSystem: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const particles = React.useMemo(() => generateParticles(PARTICLES.count), []);

  return (
    <>
      {particles.map((particle) => {
        const baseY = particle.startY - (frame * particle.speed);
        const wrappedY = ((baseY % (CANVAS.height + 100)) + (CANVAS.height + 100)) % (CANVAS.height + 100);

        const time = frame / fps;
        const xOffset = Math.sin(time * 2 + particle.id) * particle.xDrift;
        const x = particle.startX + xOffset;

        const opacity = interpolate(
          random(`particle-opacity-${particle.id}`),
          [0, 1],
          [0.3, 0.8]
        );

        return (
          <div
            key={particle.id}
            style={{
              position: 'absolute',
              left: x,
              top: wrappedY,
              width: particle.size,
              height: particle.size,
              borderRadius: '50%',
              backgroundColor: PARTICLES.color,
              opacity,
              boxShadow: `0 0 ${particle.size * 2}px ${PARTICLES.color}`,
            }}
          />
        );
      })}
    </>
  );
};
