import React from 'react';
import { useCurrentFrame, random } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS } from './constants';

interface Particle {
  id: number;
  startX: number;
  startY: number;
  opacity: number;
  speed: number;
}

const generateParticles = (count: number): Particle[] => {
  const particles: Particle[] = [];
  for (let i = 0; i < count; i++) {
    particles.push({
      id: i,
      startX: random(`closing-particle-x-${i}`) * CANVAS.width,
      startY: random(`closing-particle-y-${i}`) * CANVAS.height,
      opacity: random(`closing-particle-o-${i}`) * 0.1 + 0.15,
      speed: (random(`closing-particle-s-${i}`) * 0.3 + 0.5),
    });
  }
  return particles;
};

export const ParticleBackground: React.FC = () => {
  const frame = useCurrentFrame();
  const particles = React.useMemo(() => generateParticles(DIMENSIONS.particleCount), []);

  return (
    <>
      {particles.map((particle) => {
        const y = particle.startY - frame * particle.speed;
        const wrappedY = ((y % (CANVAS.height + 50)) + (CANVAS.height + 50)) % (CANVAS.height + 50);

        return (
          <div
            key={particle.id}
            style={{
              position: 'absolute',
              left: particle.startX,
              top: wrappedY,
              width: DIMENSIONS.particleSize,
              height: DIMENSIONS.particleSize,
              borderRadius: '50%',
              backgroundColor: COLORS.particleColor,
              opacity: particle.opacity,
            }}
          />
        );
      })}
    </>
  );
};
