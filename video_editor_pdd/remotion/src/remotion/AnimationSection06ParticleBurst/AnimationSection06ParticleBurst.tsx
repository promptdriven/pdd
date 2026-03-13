import React, { useMemo } from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  PARTICLES,
  TIMING,
  BG_RGB,
  type ParticleData,
} from './constants';
import { CenterFlash } from './CenterFlash';
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

function generateParticles(): ParticleData[] {
  const rand = mulberry32(42);
  const particles: ParticleData[] = [];

  // 20 blue circles
  for (let i = 0; i < PARTICLES.blueCount; i++) {
    particles.push({
      id: i,
      shape: 'circle',
      color: COLORS.blueParticle,
      size: lerp(PARTICLES.blueSizeRange[0], PARTICLES.blueSizeRange[1], rand()),
      angle: rand() * Math.PI * 2,
      speed: lerp(PARTICLES.speedRange[0], PARTICLES.speedRange[1], rand()),
      rotationSpeed: lerp(
        PARTICLES.rotationSpeedRange[0],
        PARTICLES.rotationSpeedRange[1],
        rand()
      ),
    });
  }

  // 20 green squares
  for (let i = 0; i < PARTICLES.greenCount; i++) {
    particles.push({
      id: PARTICLES.blueCount + i,
      shape: 'square',
      color: COLORS.greenParticle,
      size: lerp(PARTICLES.greenSizeRange[0], PARTICLES.greenSizeRange[1], rand()),
      angle: rand() * Math.PI * 2,
      speed: lerp(PARTICLES.speedRange[0], PARTICLES.speedRange[1], rand()),
      rotationSpeed: lerp(
        PARTICLES.rotationSpeedRange[0],
        PARTICLES.rotationSpeedRange[1],
        rand()
      ),
    });
  }

  return particles;
}

export const AnimationSection06ParticleBurst: React.FC = () => {
  const frame = useCurrentFrame();
  const particles = useMemo(() => generateParticles(), []);

  // Background transition: frames 10-18, easeInOutQuad
  const bgProgress = interpolate(
    frame,
    [TIMING.bgTransitionStart, TIMING.bgTransitionEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  const r = Math.round(lerp(BG_RGB.from.r, BG_RGB.to.r, bgProgress));
  const g = Math.round(lerp(BG_RGB.from.g, BG_RGB.to.g, bgProgress));
  const b = Math.round(lerp(BG_RGB.from.b, BG_RGB.to.b, bgProgress));
  const backgroundColor = `rgb(${r}, ${g}, ${b})`;

  return (
    <AbsoluteFill style={{ backgroundColor }}>
      <CenterFlash />
      {particles.map((particle) => (
        <Particle key={particle.id} particle={particle} />
      ))}
    </AbsoluteFill>
  );
};

export const defaultAnimationSection06ParticleBurstProps = {};

export default AnimationSection06ParticleBurst;
