import React, { useMemo } from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { CodeLineData, CENTER_X, CENTER_Y, CODE_LINE_COLOR } from './constants';

interface ParticleScatterProps {
  lines: CodeLineData[];
  particlesPerLine: number;
  driftRadius: number;
  fadeDuration: number;
  totalFrames: number;
}

interface Particle {
  startX: number;
  startY: number;
  angle: number;
  speed: number; // 0-1 multiplier on driftRadius
  size: number;
}

export const ParticleScatter: React.FC<ParticleScatterProps> = ({
  lines,
  particlesPerLine,
  driftRadius,
  fadeDuration,
  totalFrames,
}) => {
  const frame = useCurrentFrame();

  // Generate deterministic particles from lines
  const particles = useMemo(() => {
    const result: Particle[] = [];
    lines.forEach((line, lineIdx) => {
      const baseX = CENTER_X + line.offsetX;
      const baseY = CENTER_Y + line.offsetY;
      for (let p = 0; p < particlesPerLine; p++) {
        // Distribute particles along the line width
        const t = particlesPerLine > 1 ? p / (particlesPerLine - 1) : 0.5;
        const startX = baseX - line.width / 2 + line.width * t;
        const startY = baseY;
        // Radial angle from center, with some spread
        const dx = startX - CENTER_X;
        const dy = startY - CENTER_Y;
        const baseAngle = Math.atan2(dy, dx);
        // Add deterministic jitter
        const jitter = ((lineIdx * 7 + p * 13) % 100) / 100 - 0.5;
        const angle = baseAngle + jitter * 0.8;
        const speed = 0.5 + ((lineIdx * 3 + p * 11) % 50) / 100;
        const size = 1.5 + ((lineIdx * 5 + p * 9) % 30) / 20;
        result.push({ startX, startY, angle, speed, size });
      }
    });
    return result;
  }, [lines, particlesPerLine]);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {particles.map((particle, i) => {
        // Ease-out cubic for radial drift
        const progress = interpolate(frame, [0, totalFrames], [0, 1], {
          extrapolateRight: 'clamp',
          extrapolateLeft: 'clamp',
          easing: Easing.out(Easing.poly(3)),
        });

        const dist = driftRadius * particle.speed * progress;
        const x = particle.startX + Math.cos(particle.angle) * dist;
        const y = particle.startY + Math.sin(particle.angle) * dist;

        // Fade out over fadeDuration frames
        const opacity = interpolate(
          frame,
          [0, Math.max(1, totalFrames - fadeDuration), totalFrames],
          [0.1, 0.1, 0],
          { extrapolateRight: 'clamp', extrapolateLeft: 'clamp' }
        );

        if (opacity <= 0) return null;

        return (
          <circle
            key={i}
            cx={x}
            cy={y}
            r={particle.size * (1 - progress * 0.5)}
            fill={CODE_LINE_COLOR}
            opacity={opacity}
          />
        );
      })}
    </svg>
  );
};
