import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  PARTICLE_COUNT,
  LIQUID_COLOR,
  LIQUID_COLOR_HALF,
  LIQUID_GLOW,
  MOLD_LEFT,
  MOLD_RIGHT,
  MOLD_TOP,
  MOLD_BOTTOM,
  NOZZLE_X,
  NOISE_SCALE,
  NOISE_SPEED,
  MOLD_CENTER_X,
} from './constants';

// Simple deterministic pseudo-random based on seed
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 12.9898 + seed * 78.233) * 43758.5453;
  return x - Math.floor(x);
}

// Simple 2D noise approximation (deterministic, no external deps)
function simpleNoise(x: number, y: number, t: number): number {
  const n1 = Math.sin(x * 1.3 + t * 0.7) * Math.cos(y * 0.9 + t * 0.5);
  const n2 = Math.sin(x * 2.1 + y * 1.7 + t * 1.1) * 0.5;
  const n3 = Math.cos(x * 0.8 + y * 2.3 + t * 0.3) * 0.3;
  return (n1 + n2 + n3) / 1.8;
}

interface Particle {
  id: number;
  spawnFrame: number;
  baseX: number; // initial x offset from nozzle center
  speed: number; // downward speed multiplier
  size: number;
  noiseOffsetX: number;
  noiseOffsetY: number;
}

const LiquidFlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Generate particle pool deterministically
  const particles = useMemo<Particle[]>(() => {
    const ps: Particle[] = [];
    for (let i = 0; i < PARTICLE_COUNT; i++) {
      const r1 = seededRandom(i * 3 + 1);
      const r2 = seededRandom(i * 3 + 2);
      const r3 = seededRandom(i * 3 + 3);
      const r4 = seededRandom(i * 7 + 5);
      const r5 = seededRandom(i * 11 + 7);
      ps.push({
        id: i,
        spawnFrame: Math.floor(r1 * 120), // particles spawn over first 120 frames, then recycle
        baseX: (r2 - 0.5) * 30, // spread around nozzle
        speed: 0.6 + r3 * 0.8,
        size: 2 + r4 * 4,
        noiseOffsetX: r5 * 1000,
        noiseOffsetY: seededRandom(i * 13 + 11) * 1000,
      });
    }
    return ps;
  }, []);

  // Compute liquid fill level (how far down the cavity is filled)
  const fillLevel = interpolate(frame, [0, 280], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Cavity bounds
  const cavityTop = MOLD_TOP + 55;
  const cavityBottom = MOLD_BOTTOM - 5;
  const cavityLeft = MOLD_LEFT + 5;
  const cavityRight = MOLD_RIGHT - 5;
  const cavityH = cavityBottom - cavityTop;

  // Entry flow opacity
  const flowOpacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // After frame 280, particles start settling - reduce turbulence
  const turbulence = interpolate(frame, [250, 320], [1, 0.15], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Solidification at end
  const solidify = interpolate(frame, [300, 350], [0, 0.8], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  const time = frame * NOISE_SPEED;

  // Compute particle positions
  const renderedParticles = useMemo(() => {
    const result: Array<{
      x: number;
      y: number;
      size: number;
      opacity: number;
      id: number;
    }> = [];

    for (const p of particles) {
      // Particle lifecycle: spawns, falls, cycles
      const age = frame - p.spawnFrame;
      if (age < 0) continue;

      // Each particle cycles through the cavity
      const cycleLength = 180 / p.speed;
      const cycleAge = age % cycleLength;
      const normalizedAge = cycleAge / cycleLength;

      // Y position: falls from top, then pools at fill level
      const fallY = cavityTop + normalizedAge * cavityH;
      const fillY = cavityBottom - fillLevel * cavityH;
      const baseY = Math.min(fallY, Math.max(fillY, fallY));

      // Noise displacement
      const nx = simpleNoise(
        (p.noiseOffsetX + fallY) * NOISE_SCALE,
        time,
        p.id * 0.1
      );
      const ny = simpleNoise(
        time,
        (p.noiseOffsetY + fallY) * NOISE_SCALE,
        p.id * 0.2
      );

      // X position: starts near nozzle, spreads as it falls
      const spreadFactor = Math.min(normalizedAge * 3, 1);
      const lateralRange = (cavityRight - cavityLeft) / 2;
      let x =
        NOZZLE_X +
        p.baseX * (1 + spreadFactor * 8) +
        nx * lateralRange * 0.4 * turbulence * spreadFactor;

      let y = baseY + ny * 20 * turbulence;

      // Clamp to cavity
      x = Math.max(cavityLeft, Math.min(cavityRight, x));
      y = Math.max(cavityTop, Math.min(cavityBottom, y));

      // Opacity: fade in at spawn, brighter when settled
      const spawnFade = interpolate(cycleAge, [0, 10], [0, 1], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      });

      // Particles in the filled zone are more opaque
      const inFilledZone = y > fillY ? 0.7 : 0.4;
      const opacity = spawnFade * flowOpacity * inFilledZone;

      if (opacity > 0.01) {
        result.push({ x, y, size: p.size * (1 - solidify * 0.3), opacity, id: p.id });
      }
    }
    return result;
  }, [frame, particles, fillLevel, turbulence, solidify, flowOpacity, time,
      cavityTop, cavityBottom, cavityLeft, cavityRight, cavityH]);

  // Filled liquid body (grows from bottom)
  const filledTop = cavityBottom - fillLevel * cavityH;
  const filledBodyOpacity = interpolate(frame, [30, 60], [0, 0.25], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Final solidification color shift
  const solidColor = solidify > 0
    ? `rgba(74, 144, 217, ${0.25 + solidify * 0.35})`
    : `rgba(74, 144, 217, ${filledBodyOpacity})`;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id="particleGlow">
          <feGaussianBlur stdDeviation="3" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
        <radialGradient id="liquidGrad" cx="50%" cy="0%" r="80%">
          <stop offset="0%" stopColor={LIQUID_COLOR} stopOpacity={0.6} />
          <stop offset="100%" stopColor={LIQUID_COLOR} stopOpacity={0.1} />
        </radialGradient>
      </defs>

      {/* Filled liquid body */}
      {fillLevel > 0.02 && (
        <rect
          x={cavityLeft}
          y={filledTop}
          width={cavityRight - cavityLeft}
          height={cavityBottom - filledTop}
          fill={solidColor}
          rx={2}
        />
      )}

      {/* Entry stream from nozzle */}
      {frame < 300 && (
        <rect
          x={NOZZLE_X - 8}
          y={MOLD_TOP + 40}
          width={16}
          height={Math.min(40, frame * 2)}
          fill={LIQUID_COLOR_HALF}
          opacity={flowOpacity * 0.6}
          rx={4}
        />
      )}

      {/* Particles */}
      <g filter="url(#particleGlow)">
        {renderedParticles.map((p) => (
          <circle
            key={p.id}
            cx={p.x}
            cy={p.y}
            r={p.size}
            fill={LIQUID_COLOR}
            opacity={p.opacity}
          />
        ))}
      </g>
    </svg>
  );
};

export default LiquidFlow;
