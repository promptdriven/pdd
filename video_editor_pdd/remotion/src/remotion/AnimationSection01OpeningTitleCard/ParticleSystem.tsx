import React from 'react';
import { useCurrentFrame, useVideoConfig } from 'remotion';
import { PARTICLES, COLORS } from './constants';

interface Particle {
  id: number;
  x: number;
  y: number;
  size: number;
  opacity: number;
  speedY: number;
  oscillationSpeed: number;
  oscillationAmplitude: number;
}

const generateParticles = (): Particle[] => {
  const particles: Particle[] = [];
  for (let i = 0; i < PARTICLES.count; i++) {
    particles.push({
      id: i,
      x: Math.random() * 1920,
      y: Math.random() * 1080,
      size: PARTICLES.sizeMin + Math.random() * (PARTICLES.sizeMax - PARTICLES.sizeMin),
      opacity: PARTICLES.opacityMin + Math.random() * (PARTICLES.opacityMax - PARTICLES.opacityMin),
      speedY: 0.3 + Math.random() * 0.5,
      oscillationSpeed: 0.02 + Math.random() * 0.03,
      oscillationAmplitude: 10 + Math.random() * 20,
    });
  }
  return particles;
};

const particles = generateParticles();

export const ParticleSystem: React.FC = () => {
  const frame = useCurrentFrame();
  const { height } = useVideoConfig();

  return (
    <>
      {particles.map((particle) => {
        const yPos = (particle.y - particle.speedY * frame) % (height + 100);
        const adjustedY = yPos < -50 ? height + 50 : yPos;
        const xOffset = Math.sin(frame * particle.oscillationSpeed) * particle.oscillationAmplitude;
        const xPos = particle.x + xOffset;

        return (
          <div
            key={particle.id}
            style={{
              position: 'absolute',
              left: xPos,
              top: adjustedY,
              width: particle.size,
              height: particle.size,
              borderRadius: '50%',
              backgroundColor: COLORS.accentBlue,
              opacity: particle.opacity,
              pointerEvents: 'none',
            }}
          />
        );
      })}
    </>
  );
};
