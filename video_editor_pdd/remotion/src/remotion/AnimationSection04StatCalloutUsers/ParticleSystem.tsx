/**
 * ParticleSystem component
 * Renders floating particles with continuous drift and opacity oscillation
 */

import React from 'react';
import { useCurrentFrame } from 'remotion';
import { COLORS, ANIMATION, CANVAS } from './constants';

interface Particle {
  id: number;
  x: number;
  y: number;
  radius: number;
  speedX: number;
  speedY: number;
  phase: number;
}

const generateParticles = (): Particle[] => {
  const particles: Particle[] = [];
  for (let i = 0; i < ANIMATION.PARTICLE_COUNT; i++) {
    particles.push({
      id: i,
      x: Math.random() * CANVAS.WIDTH,
      y: Math.random() * CANVAS.HEIGHT,
      radius: 2 + Math.random() * 4,
      speedX: (Math.random() - 0.5) * 2,
      speedY: -0.5 - Math.random() * 1.5,
      phase: Math.random() * Math.PI * 2,
    });
  }
  return particles;
};

const particles = generateParticles();

export const ParticleSystem: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <>
      {particles.map((particle) => {
        // Calculate position with wrapping
        let x = particle.x + particle.speedX * frame;
        let y = particle.y + particle.speedY * frame;

        // Wrap around screen
        x = ((x % CANVAS.WIDTH) + CANVAS.WIDTH) % CANVAS.WIDTH;
        y = ((y % CANVAS.HEIGHT) + CANVAS.HEIGHT) % CANVAS.HEIGHT;

        // Oscillating opacity
        const opacity = 0.2 + 0.3 * Math.sin(frame / 30 + particle.phase);

        return (
          <div
            key={particle.id}
            style={{
              position: 'absolute',
              left: x,
              top: y,
              width: particle.radius * 2,
              height: particle.radius * 2,
              borderRadius: '50%',
              backgroundColor: COLORS.PARTICLE,
              opacity,
              transform: 'translate(-50%, -50%)',
            }}
          />
        );
      })}
    </>
  );
};
