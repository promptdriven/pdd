import React, { useMemo } from 'react';
import { AbsoluteFill } from 'remotion';
import { CANVAS, COLORS, PARTICLES, type ParticleData } from './constants';
import { FlashOverlay } from './FlashOverlay';
import { Particle } from './Particle';

/**
 * Seeded pseudo-random number generator (mulberry32) for deterministic
 * particle layout across renders.
 */
function mulberry32(seed: number) {
  let s = seed;
  return () => {
    s |= 0;
    s = (s + 0x6d2b79f5) | 0;
    const t0 = Math.imul(s ^ (s >>> 15), 1 | s);
    const t1 = (t0 + Math.imul(t0 ^ (t0 >>> 7), 61 | t0)) ^ t0;
    return ((t1 ^ (t1 >>> 14)) >>> 0) / 4294967296;
  };
}

function lerp(a: number, b: number, t: number): number {
  return a + (b - a) * t;
}

function degToRad(deg: number): number {
  return (deg * Math.PI) / 180;
}

function generateParticles(): ParticleData[] {
  const rand = mulberry32(PARTICLES.seed);
  const particles: ParticleData[] = [];
  const baseAngleStep = (2 * Math.PI) / PARTICLES.count;

  for (let i = 0; i < PARTICLES.count; i++) {
    // Evenly distributed angles with slight random jitter (+/- 5 degrees)
    const baseAngle = i * baseAngleStep;
    const jitter = degToRad((rand() * 2 - 1) * PARTICLES.angleJitter);
    const angle = baseAngle + jitter;

    // Random radius between min and max
    const radius = lerp(PARTICLES.minRadius, PARTICLES.maxRadius, rand());

    // Random travel distance between min and max
    const distance = lerp(PARTICLES.minDistance, PARTICLES.maxDistance, rand());

    // Random color from palette
    const colorIndex = Math.floor(rand() * COLORS.particles.length);
    const color = COLORS.particles[colorIndex];

    particles.push({ id: i, color, radius, angle, distance });
  }

  return particles;
}

export const AnimationSection06ParticleBurst: React.FC = () => {
  const particles = useMemo(() => generateParticles(), []);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        width: CANVAS.width,
        height: CANVAS.height,
      }}
    >
      <FlashOverlay />
      {particles.map((particle) => (
        <Particle key={particle.id} particle={particle} />
      ))}
    </AbsoluteFill>
  );
};

export const defaultAnimationSection06ParticleBurstProps = {};

export default AnimationSection06ParticleBurst;
