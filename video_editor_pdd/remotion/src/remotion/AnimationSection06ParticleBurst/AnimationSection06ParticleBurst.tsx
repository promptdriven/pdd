import React, { useMemo } from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, PARTICLE_CONFIG, TIMING, type ParticleData } from './constants';
import { CenterFlash } from './CenterFlash';
import { Particle } from './Particle';

/**
 * Attempt a seeded pseudo-random number generator so particle layout
 * is deterministic across renders. Uses a simple mulberry32 algorithm.
 */
function mulberry32(seed: number) {
  let s = seed;
  return () => {
    s |= 0;
    s = (s + 0x6d2b79f5) | 0;
    let t = Math.imul(s ^ (s >>> 15), 1 | s);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function lerp(min: number, max: number, t: number): number {
  return min + (max - min) * t;
}

function generateParticles(): ParticleData[] {
  const rand = mulberry32(42);
  const particles: ParticleData[] = [];

  // Blue particles (circles)
  for (let i = 0; i < PARTICLE_CONFIG.blueCount; i++) {
    particles.push({
      id: i,
      shape: 'circle',
      color: COLORS.blue,
      size: lerp(PARTICLE_CONFIG.blueSizeRange[0], PARTICLE_CONFIG.blueSizeRange[1], rand()),
      angle: rand() * Math.PI * 2,
      speed: lerp(PARTICLE_CONFIG.speedRange[0], PARTICLE_CONFIG.speedRange[1], rand()),
      rotationSpeed: lerp(-8, 8, rand()),
    });
  }

  // Green particles (squares)
  for (let i = 0; i < PARTICLE_CONFIG.greenCount; i++) {
    particles.push({
      id: PARTICLE_CONFIG.blueCount + i,
      shape: 'square',
      color: COLORS.green,
      size: lerp(PARTICLE_CONFIG.greenSizeRange[0], PARTICLE_CONFIG.greenSizeRange[1], rand()),
      angle: rand() * Math.PI * 2,
      speed: lerp(PARTICLE_CONFIG.speedRange[0], PARTICLE_CONFIG.speedRange[1], rand()),
      rotationSpeed: lerp(-8, 8, rand()),
    });
  }

  return particles;
}

export const AnimationSection06ParticleBurst: React.FC = () => {
  const frame = useCurrentFrame();
  const particles = useMemo(() => generateParticles(), []);

  // Background transition from charcoal to dark navy (frames 30-50)
  const bgProgress = interpolate(
    frame,
    [TIMING.bgTransitionStart, TIMING.bgTransitionEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  // Interpolate RGB components for background color
  // #141921 = rgb(20, 25, 33)
  // #0B1120 = rgb(11, 17, 32)
  const r = Math.round(lerp(20, 11, bgProgress));
  const g = Math.round(lerp(25, 17, bgProgress));
  const b = Math.round(lerp(33, 32, bgProgress));
  const backgroundColor = `rgb(${r}, ${g}, ${b})`;

  return (
    <AbsoluteFill
      style={{
        backgroundColor,
      }}
    >
      <CenterFlash />
      {particles.map((particle) => (
        <Particle key={particle.id} particle={particle} />
      ))}
    </AbsoluteFill>
  );
};

export const defaultAnimationSection06ParticleBurstProps = {};

export default AnimationSection06ParticleBurst;
