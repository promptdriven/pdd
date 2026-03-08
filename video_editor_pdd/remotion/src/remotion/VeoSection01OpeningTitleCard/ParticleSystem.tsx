/**
 * ParticleSystem Component
 *
 * Renders a subtle particle system with drifting circles for depth and premium feel
 */

import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, DIMENSIONS } from './constants';

interface Particle {
  id: number;
  x: number;
  y: number;
  size: number;
  opacity: number;
  driftX: number;
  driftY: number;
}

// Generate particles with deterministic positions
const generateParticles = (count: number): Particle[] => {
  const particles: Particle[] = [];

  for (let i = 0; i < count; i++) {
    // Use index-based pseudo-random values for deterministic rendering
    const seed1 = (i * 7919) % 1000;
    const seed2 = (i * 5381) % 1000;
    const seed3 = (i * 2729) % 1000;
    const seed4 = (i * 1009) % 1000;
    const seed5 = (i * 4603) % 1000;
    const seed6 = (i * 3607) % 1000;

    particles.push({
      id: i,
      x: (seed1 / 1000) * DIMENSIONS.canvas.width,
      y: (seed2 / 1000) * DIMENSIONS.canvas.height,
      size: DIMENSIONS.particle.minSize + (seed3 / 1000) * (DIMENSIONS.particle.maxSize - DIMENSIONS.particle.minSize),
      opacity: 0.1 + (seed4 / 1000) * 0.3,
      driftX: (seed5 / 1000) - 0.5,
      driftY: (seed6 / 1000) - 0.5,
    });
  }

  return particles;
};

const particles = generateParticles(DIMENSIONS.particle.count);

export const ParticleSystem: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <>
      {particles.map((particle) => {
        // Subtle drift animation
        const offsetX = particle.driftX * frame * 0.5;
        const offsetY = particle.driftY * frame * 0.3;

        return (
          <div
            key={particle.id}
            style={{
              position: 'absolute',
              left: particle.x + offsetX,
              top: particle.y + offsetY,
              width: particle.size,
              height: particle.size,
              borderRadius: '50%',
              backgroundColor: COLORS.particle,
              opacity: particle.opacity,
            }}
          />
        );
      })}
    </>
  );
};
