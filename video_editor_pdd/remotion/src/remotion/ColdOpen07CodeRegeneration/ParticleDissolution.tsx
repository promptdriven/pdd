import React, { useMemo } from 'react';
import { interpolate, Easing } from 'remotion';
import {
  PATCHED_CODE_LINES,
  LINE_HEIGHT,
  CODE_LEFT_PADDING,
  CODE_TOP_PADDING,
  CODE_FONT_SIZE,
  DISSOLUTION_STAGGER_PER_LINE,
  PARTICLE_FADE_DURATION,
  CODE_TEXT_COLOR,
  SYN_COMMENT,
  DISSOLUTION_GLOW_COLOR,
  DISSOLUTION_GLOW_OPACITY,
} from './constants';

// ── Particle seed generation ────────────────────────────────────────────────

interface Particle {
  x: number;
  y: number;
  color: string;
  // random drift velocities (per frame, scaled)
  vx: number;
  vy: number;
  /** Frame offset from dissolution start for this particle's line */
  lineDelay: number;
}

/** Simple deterministic pseudo-random from seed */
function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return (s - 1) / 2147483646;
  };
}

function buildParticles(lines: string[]): Particle[] {
  const particles: Particle[] = [];
  const rand = seededRandom(42);
  const charWidth = CODE_FONT_SIZE * 0.6; // approx monospace char width at 18px

  const totalLines = lines.length;

  for (let lineIdx = 0; lineIdx < totalLines; lineIdx++) {
    const line = lines[lineIdx];
    // Bottom-to-top stagger: bottom line starts first
    const lineDelay = (totalLines - 1 - lineIdx) * DISSOLUTION_STAGGER_PER_LINE;
    const isComment = line.trimStart().startsWith('//');
    const baseColor = isComment ? SYN_COMMENT : CODE_TEXT_COLOR;

    for (let charIdx = 0; charIdx < line.length; charIdx++) {
      if (line[charIdx] === ' ') continue; // skip spaces

      const x = CODE_LEFT_PADDING + charIdx * charWidth;
      const y = CODE_TOP_PADDING + lineIdx * LINE_HEIGHT;

      // Random drift: y velocity -40 to -80 px/s → per frame at 30fps: -1.33 to -2.67
      const vy = -(40 + rand() * 40) / 30;
      // x velocity: -20 to +20 px/s → per frame: -0.67 to +0.67
      const vx = (-20 + rand() * 40) / 30;

      particles.push({
        x,
        y,
        color: baseColor,
        vx,
        vy,
        lineDelay,
      });
    }
  }

  return particles;
}

// ── Component ───────────────────────────────────────────────────────────────

interface ParticleDissolutionProps {
  /** Frame offset within dissolution phase (0 = dissolution start) */
  phaseFrame: number;
}

const ParticleDissolution: React.FC<ParticleDissolutionProps> = ({ phaseFrame }) => {
  const particles = useMemo(() => buildParticles(PATCHED_CODE_LINES), []);

  // Radial glow pulse
  const glowOpacity = interpolate(
    phaseFrame,
    [0, 15, 30, 55],
    [0, DISSOLUTION_GLOW_OPACITY, DISSOLUTION_GLOW_OPACITY * 0.5, 0],
    { extrapolateRight: 'clamp', extrapolateLeft: 'clamp' },
  );

  return (
    <>
      {/* Background radial glow */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
          background: `radial-gradient(ellipse at 50% 40%, ${DISSOLUTION_GLOW_COLOR} 0%, transparent 70%)`,
          opacity: glowOpacity,
          pointerEvents: 'none',
        }}
      />
      {/* Particles */}
      <svg
        width="100%"
        height="100%"
        style={{ position: 'absolute', top: 0, left: 0, overflow: 'visible' }}
      >
        {particles.map((p, i) => {
          const localFrame = phaseFrame - p.lineDelay;
          if (localFrame < 0) {
            // Not yet started dissolving — render as static 2x2 square
            return (
              <rect
                key={i}
                x={p.x}
                y={p.y}
                width={2}
                height={2}
                fill={p.color}
              />
            );
          }

          // Particle has begun dissolving
          const driftEased = interpolate(
            localFrame,
            [0, PARTICLE_FADE_DURATION],
            [0, 1],
            { extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) },
          );

          const dx = p.vx * localFrame;
          const dy = p.vy * localFrame * (1 + driftEased * 0.5);

          const opacity = interpolate(
            localFrame,
            [0, PARTICLE_FADE_DURATION],
            [1, 0],
            { extrapolateRight: 'clamp' },
          );

          if (opacity <= 0) return null;

          return (
            <rect
              key={i}
              x={p.x + dx}
              y={p.y + dy}
              width={2}
              height={2}
              fill={p.color}
              opacity={opacity}
            />
          );
        })}
      </svg>
    </>
  );
};

export default ParticleDissolution;
