import React, { useMemo } from 'react';
import { AbsoluteFill } from 'remotion';
import { CANVAS, COLORS, PARTICLES, TIMING, type ParticleData } from './constants';
import { CentralFlash } from './CentralFlash';
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

/**
 * Generate 40 deterministic particles with random angle, speed, radius, and color.
 * Larger particles move slightly slower per the spec.
 */
function generateParticles(): ParticleData[] {
  const rand = mulberry32(PARTICLES.seed);
  const particles: ParticleData[] = [];

  for (let i = 0; i < PARTICLES.count; i++) {
    // Random angle 0-360 degrees (full circle)
    const angle = rand() * 2 * Math.PI;

    // Random radius between 3-8px
    const radius = lerp(PARTICLES.minRadius, PARTICLES.maxRadius, rand());

    // Speed inversely scaled by radius — larger particles move slightly slower
    const radiusNorm = (radius - PARTICLES.minRadius) / (PARTICLES.maxRadius - PARTICLES.minRadius);
    const baseSpeed = lerp(PARTICLES.minSpeed, PARTICLES.maxSpeed, rand());
    const speed = baseSpeed * (1 - radiusNorm * 0.3); // up to 30% slower for largest

    // Max distance capped at 300px per spec
    const moveDuration = (TIMING.particleMoveEnd - TIMING.particleStart) / TIMING.fps;
    const maxDistance = Math.min(PARTICLES.maxDistance, speed * moveDuration);

    // Color distributed evenly across palette
    const colorIndex = i % COLORS.particles.length;
    const color = COLORS.particles[colorIndex];

    particles.push({ id: i, color, radius, angle, speed, maxDistance });
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
      <CentralFlash />
      {particles.map((particle) => (
        <Particle key={particle.id} particle={particle} />
      ))}
    </AbsoluteFill>
  );
};

export const defaultAnimationSection06ParticleBurstProps = {};

export default AnimationSection06ParticleBurst;
