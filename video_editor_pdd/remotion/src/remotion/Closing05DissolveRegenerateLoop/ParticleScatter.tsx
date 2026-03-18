// ParticleScatter.tsx — Code lines dissolving into radial particles
import React, { useMemo } from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { CODE_COLOR, TRIANGLE } from './constants';

interface CodeLineSpec {
  readonly width: number;
  readonly offsetX: number;
  readonly offsetY: number;
}

interface Particle {
  startX: number;
  startY: number;
  angle: number; // radial direction
  speed: number; // drift speed multiplier
  size: number;
}

interface ParticleScatterProps {
  lines: readonly CodeLineSpec[];
  centerX: number;
  centerY: number;
  particlesPerLine: number;
  driftRadius: number;
  fadeDuration: number;
  totalDuration: number;
}

// Seeded pseudo-random for deterministic particles
function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return (s - 1) / 2147483646;
  };
}

export const ParticleScatter: React.FC<ParticleScatterProps> = ({
  lines,
  centerX,
  centerY,
  particlesPerLine,
  driftRadius,
  fadeDuration,
  totalDuration,
}) => {
  const frame = useCurrentFrame();

  // Generate deterministic particles from each code line
  const particles = useMemo(() => {
    const rng = seededRandom(
      lines.length * 1000 + particlesPerLine * 100 + driftRadius
    );
    const result: Particle[] = [];

    for (const line of lines) {
      const lineX = centerX + line.offsetX;
      const lineY = centerY + line.offsetY;

      for (let p = 0; p < particlesPerLine; p++) {
        const startX = lineX - line.width / 2 + rng() * line.width;
        const startY = lineY + (rng() - 0.5) * 4;
        const angle = Math.atan2(startY - centerY, startX - centerX) + (rng() - 0.5) * 0.5;
        const speed = 0.5 + rng() * 0.8;
        const size = 1.5 + rng() * 2.5;

        result.push({ startX, startY, angle, speed, size });
      }
    }

    return result;
  }, [lines, centerX, centerY, particlesPerLine, driftRadius]);

  // Triangle boundary check — particles should dissipate before edges
  const maxDist = driftRadius * 0.85;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {particles.map((particle, i) => {
        // Eased progress
        const progress = interpolate(frame, [0, totalDuration], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.cubic),
        });

        const dist = progress * driftRadius * particle.speed;
        const clampedDist = Math.min(dist, maxDist);

        const x = particle.startX + Math.cos(particle.angle) * clampedDist;
        const y = particle.startY + Math.sin(particle.angle) * clampedDist;

        // Fade out over fadeDuration frames
        const opacity = interpolate(
          frame,
          [0, Math.max(1, totalDuration - fadeDuration), totalDuration],
          [0.1, 0.1, 0],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );

        if (opacity <= 0) return null;

        return (
          <circle
            key={i}
            cx={x}
            cy={y}
            r={particle.size}
            fill={CODE_COLOR}
            opacity={opacity}
          />
        );
      })}
    </svg>
  );
};
