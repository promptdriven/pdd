import React from 'react';
import { useCurrentFrame, useVideoConfig, random } from 'remotion';
import { PARTICLES, CANVAS } from './constants';

interface Particle {
  id: number;
  startX: number;
  startY: number;
  size: number;
  speed: number;
  xDrift: number;
  opacity: number;
}

const generateParticles = (count: number): Particle[] => {
  const particles: Particle[] = [];
  for (let i = 0; i < count; i++) {
    particles.push({
      id: i,
      startX: random(`closing-particle-x-${i}`) * CANVAS.width,
      startY: random(`closing-particle-y-${i}`) * CANVAS.height,
      size:
        random(`closing-particle-size-${i}`) *
          (PARTICLES.maxSize - PARTICLES.minSize) +
        PARTICLES.minSize,
      speed: (random(`closing-particle-speed-${i}`) * 0.5 + 0.75) * PARTICLES.speed,
      xDrift: (random(`closing-particle-drift-${i}`) - 0.5) * 60,
      opacity:
        random(`closing-particle-opacity-${i}`) *
          (PARTICLES.opacityMax - PARTICLES.opacityMin) +
        PARTICLES.opacityMin,
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
        const baseY = particle.startY - frame * particle.speed;
        const wrappedY =
          ((baseY % (CANVAS.height + 100)) + (CANVAS.height + 100)) %
          (CANVAS.height + 100);

        const time = frame / fps;
        const xOffset = Math.sin(time * 2 + particle.id) * particle.xDrift;
        const x = particle.startX + xOffset;

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
              opacity: particle.opacity,
              boxShadow: `0 0 ${particle.size * 2}px ${PARTICLES.color}`,
            }}
          />
        );
      })}
    </>
  );
};
