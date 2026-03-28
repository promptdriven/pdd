import React, { useMemo } from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CODE_BLOCK_CENTER_X,
  CODE_BLOCK_CENTER_Y,
  CODE_BLOCK_WIDTH,
  CODE_BLOCK_HEIGHT,
  PARTICLE_SIZE,
  PARTICLE_MIN_DRIFT,
  PARTICLE_MAX_DRIFT,
  PARTICLE_MIN_DURATION,
  PARTICLE_MAX_DURATION,
  SYNTAX_KEYWORD,
  SYNTAX_STRING,
  SYNTAX_FUNCTION,
  SYNTAX_DEFAULT,
  CodeLine,
} from './constants';

// Seeded pseudo-random for deterministic particle generation
function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return (s - 1) / 2147483646;
  };
}

function getSyntaxColor(char: string, colIndex: number, lineText: string): string {
  // Simple heuristic: keywords at start, strings in quotes, else default
  const keywords = ['def', 'for', 'in', 'return', 'import'];
  const trimmed = lineText.trimStart();
  for (const kw of keywords) {
    if (trimmed.startsWith(kw)) {
      const kwStart = lineText.indexOf(kw);
      if (colIndex >= kwStart && colIndex < kwStart + kw.length) {
        return SYNTAX_KEYWORD;
      }
    }
  }
  // Function names (after 'def ')
  if (trimmed.startsWith('def ')) {
    const defIdx = lineText.indexOf('def ');
    const afterDef = defIdx + 4;
    const parenIdx = lineText.indexOf('(', afterDef);
    if (colIndex >= afterDef && colIndex < (parenIdx > 0 ? parenIdx : lineText.length)) {
      return SYNTAX_FUNCTION;
    }
  }
  // Strings in quotes
  if (lineText.includes("'") || lineText.includes('"')) {
    return colIndex % 3 === 0 ? SYNTAX_STRING : SYNTAX_DEFAULT;
  }
  return SYNTAX_DEFAULT;
}

interface Particle {
  x: number;
  y: number;
  color: string;
  angle: number;
  drift: number;
  duration: number;
  delay: number;
}

function generateParticles(code: CodeLine[], seed: number): Particle[] {
  const rand = seededRandom(seed);
  const particles: Particle[] = [];

  const blockLeft = CODE_BLOCK_CENTER_X - CODE_BLOCK_WIDTH / 2 + 16;
  const blockTop = CODE_BLOCK_CENTER_Y - CODE_BLOCK_HEIGHT / 2 + 20;
  const charW = 7.8; // approximate monospace char width at 13px
  const lineH = 20;

  for (let lineIdx = 0; lineIdx < code.length; lineIdx++) {
    const line = code[lineIdx].text;
    for (let charIdx = 0; charIdx < line.length; charIdx++) {
      if (line[charIdx] === ' ') continue;
      particles.push({
        x: blockLeft + charIdx * charW,
        y: blockTop + lineIdx * lineH,
        color: getSyntaxColor(line[charIdx], charIdx, line),
        angle: rand() * Math.PI * 2,
        drift: PARTICLE_MIN_DRIFT + rand() * (PARTICLE_MAX_DRIFT - PARTICLE_MIN_DRIFT),
        duration: PARTICLE_MIN_DURATION + rand() * (PARTICLE_MAX_DURATION - PARTICLE_MIN_DURATION),
        delay: rand() * 5, // slight stagger
      });
    }
  }
  return particles;
}

interface DissolveParticlesProps {
  code: CodeLine[];
  dissolveStartFrame: number;
  dissolveDuration: number;
  seed: number;
}

const DissolveParticles: React.FC<DissolveParticlesProps> = ({
  code,
  dissolveStartFrame,
  dissolveDuration,
  seed,
}) => {
  const frame = useCurrentFrame();
  const particles = useMemo(() => generateParticles(code, seed), [code, seed]);

  const dissolveProgress = frame - dissolveStartFrame;
  if (dissolveProgress < 0 || dissolveProgress > dissolveDuration + PARTICLE_MAX_DURATION + 5) {
    return null;
  }

  return (
    <div style={{ position: 'absolute', top: 0, left: 0, width: '100%', height: '100%' }}>
      {particles.map((p, i) => {
        const localFrame = dissolveProgress - p.delay;
        if (localFrame < 0 || localFrame > p.duration) return null;

        const progress = interpolate(localFrame, [0, p.duration], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.cubic),
        });

        const dx = Math.cos(p.angle) * p.drift * progress;
        const dy = Math.sin(p.angle) * p.drift * progress;
        const opacity = interpolate(progress, [0, 0.3, 1], [0.8, 0.6, 0], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        });

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: p.x + dx,
              top: p.y + dy,
              width: PARTICLE_SIZE,
              height: PARTICLE_SIZE,
              backgroundColor: p.color,
              opacity,
              borderRadius: 1,
            }}
          />
        );
      })}
    </div>
  );
};

export default DissolveParticles;
