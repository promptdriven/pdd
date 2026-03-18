import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing, AbsoluteFill } from 'remotion';
import {
  PARTICLE_COUNT,
  PARTICLE_GRAVITY,
  PARTICLE_MIN_SIZE,
  PARTICLE_MAX_SIZE,
  PARTICLE_FADE_DURATION,
  OLD_CODE,
  TOKEN_COLORS,
  EDITOR_LEFT,
  TAB_BAR_HEIGHT,
  LINE_HEIGHT,
  CodeLine,
} from './constants';

interface Particle {
  x: number;
  y: number;
  size: number;
  color: string;
  vx: number; // horizontal drift velocity
  delay: number; // stagger frames (0-5)
}

/**
 * Generates a deterministic set of particles derived from old code positions.
 * Each particle inherits a syntax color and starts near a character position.
 */
function generateParticles(codeLines: CodeLine[]): Particle[] {
  const particles: Particle[] = [];
  const allColors: string[] = [];

  // Collect all character-level colors from old code
  for (const line of codeLines) {
    for (const token of line.tokens) {
      const color = TOKEN_COLORS[token.type];
      for (let i = 0; i < token.text.length; i++) {
        allColors.push(color);
      }
    }
  }

  // Seeded pseudo-random (deterministic across renders)
  let seed = 42;
  const rand = () => {
    seed = (seed * 16807 + 0) % 2147483647;
    return (seed - 1) / 2147483646;
  };

  for (let i = 0; i < PARTICLE_COUNT; i++) {
    // Distribute particles across the 18 lines
    const lineIdx = Math.floor(rand() * codeLines.length);
    const line = codeLines[lineIdx];
    const charCount = line.tokens.reduce((s, t) => s + t.text.length, 0);
    const charIdx = Math.floor(rand() * Math.max(charCount, 1));

    // Pick a color from the token at that char position
    let colorIdx = 0;
    let acc = 0;
    for (const token of line.tokens) {
      acc += token.text.length;
      if (charIdx < acc) {
        break;
      }
      colorIdx += token.text.length;
    }
    const globalIdx = (() => {
      let total = 0;
      for (let l = 0; l < lineIdx; l++) {
        for (const t of codeLines[l].tokens) total += t.text.length;
      }
      return total + charIdx;
    })();

    const color = allColors[globalIdx % allColors.length] || '#C9D1D9';

    particles.push({
      x: EDITOR_LEFT + charIdx * 8.4, // approximate monospace char width at 14px
      y: TAB_BAR_HEIGHT + lineIdx * LINE_HEIGHT + 6,
      size: PARTICLE_MIN_SIZE + rand() * (PARTICLE_MAX_SIZE - PARTICLE_MIN_SIZE),
      color,
      vx: (rand() - 0.5) * 2, // drift range [-1, 1]
      delay: Math.floor(rand() * 5),
    });
  }

  return particles;
}

const ParticleDissolve: React.FC = () => {
  const frame = useCurrentFrame();
  const particles = useMemo(() => generateParticles(OLD_CODE), []);

  return (
    <AbsoluteFill>
      {particles.map((p, i) => {
        const localFrame = Math.max(0, frame - p.delay);
        const t = localFrame; // time in frames since this particle started

        // Gravity: easeIn(quad) vertical displacement
        const dy = 0.5 * PARTICLE_GRAVITY * t * t;
        // Horizontal drift: linear
        const dx = p.vx * t;

        // Fade: easeIn(cubic) over PARTICLE_FADE_DURATION frames
        const opacity = interpolate(
          localFrame,
          [0, PARTICLE_FADE_DURATION],
          [1, 0],
          {
            easing: Easing.in(Easing.cubic),
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          },
        );

        if (opacity <= 0) return null;

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: p.x + dx,
              top: p.y + dy,
              width: p.size,
              height: p.size,
              borderRadius: '50%',
              backgroundColor: p.color,
              opacity,
              willChange: 'transform',
            }}
          />
        );
      })}
    </AbsoluteFill>
  );
};

export default ParticleDissolve;
