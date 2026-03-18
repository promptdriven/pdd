import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  PARTICLE_COUNT,
  PARTICLE_COLORS,
  PARTICLE_SPEED_RANGE,
  PARTICLE_SIZE_RANGE,
  PARTICLE_OPACITY_RANGE,
  PARTICLE_SPAWN_Y_RANGE,
  WIDTH,
  DURATION_FRAMES,
} from './constants';

// Deterministic pseudo-random from seed
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 127.1 + 311.7) * 43758.5453;
  return x - Math.floor(x);
}

interface Particle {
  x: number;
  startY: number;
  speed: number;
  size: number;
  color: string;
  opacity: number;
  spawnFrame: number;
}

function generateParticles(count: number): Particle[] {
  const particles: Particle[] = [];
  for (let i = 0; i < count; i++) {
    const r0 = seededRandom(i * 3 + 0);
    const r1 = seededRandom(i * 3 + 1);
    const r2 = seededRandom(i * 3 + 2);
    const r3 = seededRandom(i * 3 + 3);
    const r4 = seededRandom(i * 3 + 4);
    const r5 = seededRandom(i * 3 + 5);

    particles.push({
      x: r0 * WIDTH,
      startY:
        PARTICLE_SPAWN_Y_RANGE[0] +
        r1 * (PARTICLE_SPAWN_Y_RANGE[1] - PARTICLE_SPAWN_Y_RANGE[0]),
      speed:
        PARTICLE_SPEED_RANGE[0] +
        r2 * (PARTICLE_SPEED_RANGE[1] - PARTICLE_SPEED_RANGE[0]),
      size:
        PARTICLE_SIZE_RANGE[0] +
        r3 * (PARTICLE_SIZE_RANGE[1] - PARTICLE_SIZE_RANGE[0]),
      color: PARTICLE_COLORS[Math.floor(r4 * PARTICLE_COLORS.length)],
      opacity:
        PARTICLE_OPACITY_RANGE[0] +
        r5 * (PARTICLE_OPACITY_RANGE[1] - PARTICLE_OPACITY_RANGE[0]),
      spawnFrame: Math.floor(r0 * 60), // stagger spawns over first 2s
    });
  }
  return particles;
}

export const ParticleField: React.FC = () => {
  const frame = useCurrentFrame();
  const particles = useMemo(() => generateParticles(PARTICLE_COUNT), []);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {particles.map((p, i) => {
        const elapsed = frame - p.spawnFrame;
        if (elapsed < 0) return null;

        const y = p.startY - elapsed * p.speed;
        if (y < -10) return null;

        // Fade in over first 30 frames after spawn
        const fadeIn = interpolate(elapsed, [0, 30], [0, 1], {
          extrapolateRight: 'clamp',
        });

        // Fade out as particle approaches top (y < 200)
        const fadeOut = interpolate(y, [0, 200], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.quad),
        });

        const opacity = p.opacity * fadeIn * fadeOut;

        return (
          <circle
            key={i}
            cx={p.x}
            cy={y}
            r={p.size}
            fill={p.color}
            opacity={opacity}
          />
        );
      })}
    </svg>
  );
};
