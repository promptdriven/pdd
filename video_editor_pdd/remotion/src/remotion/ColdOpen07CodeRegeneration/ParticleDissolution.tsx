import React, { useMemo } from 'react';
import { interpolate, Easing } from 'remotion';
import { tokenizeLine } from './SyntaxHighlighter';
import {
  CODE_LEFT_PADDING,
  CODE_TOP_PADDING,
  GUTTER_WIDTH,
  LINE_HEIGHT,
  CODE_FONT_SIZE,
  DISSOLUTION_STAGGER_FRAMES,
  DISSOLUTION_FADE_DURATION,
  DISSOLUTION_PARTICLE_SIZE,
  DISSOLUTION_GLOW_COLOR,
  DISSOLUTION_GLOW_OPACITY,
} from './constants';

/** A single particle derived from a character in the code */
interface Particle {
  /** Original x position (px) */
  x: number;
  /** Original y position (px) */
  y: number;
  /** Color of the character */
  color: string;
  /** Random x velocity (px/frame) */
  vx: number;
  /** Random y velocity (px/frame, negative = upward) */
  vy: number;
  /** Frame offset when this particle starts dissolving (stagger) */
  startFrame: number;
}

// Deterministic pseudo-random from seed
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 9301 + 49297) * 49271;
  return x - Math.floor(x);
}

interface ParticleDissolutionProps {
  /** Lines of code to dissolve */
  codeLines: string[];
  /** Relative frame within the dissolution phase (0 = start of dissolution) */
  phaseFrame: number;
  /** Total frames for the dissolution phase */
  phaseDuration: number;
}

export const ParticleDissolution: React.FC<ParticleDissolutionProps> = ({
  codeLines,
  phaseFrame,
  phaseDuration,
}) => {
  // Pre-compute all particles from the code lines
  const particles = useMemo(() => {
    const result: Particle[] = [];
    const totalLines = codeLines.length;
    // Approximate character width for monospace at 18px
    const charWidth = CODE_FONT_SIZE * 0.6;

    for (let lineIdx = 0; lineIdx < totalLines; lineIdx++) {
      const line = codeLines[lineIdx];
      if (!line) continue;

      const tokens = tokenizeLine(line);
      let charOffset = 0;

      for (const token of tokens) {
        for (let c = 0; c < token.text.length; c++) {
          if (token.text[c] === ' ') {
            charOffset++;
            continue;
          }

          const x = GUTTER_WIDTH + CODE_LEFT_PADDING + charOffset * charWidth;
          const y = CODE_TOP_PADDING + lineIdx * LINE_HEIGHT;

          // Bottom-to-top: last line dissolves first
          const reverseLineIdx = totalLines - 1 - lineIdx;
          const startFrame = reverseLineIdx * DISSOLUTION_STAGGER_FRAMES;

          const seed = lineIdx * 1000 + charOffset;
          const vx = (seededRandom(seed) - 0.5) * (40 / 30); // -20 to +20 px/s → per-frame
          const vy = -(seededRandom(seed + 1) * (40 / 30) + (40 / 30)); // -40 to -80 px/s → per-frame

          result.push({
            x,
            y,
            color: token.color,
            vx,
            vy,
            startFrame,
          });

          charOffset++;
        }
      }
    }
    return result;
  }, [codeLines]);

  // Glow pulse progress (0→1 over the phase)
  const glowOpacity = interpolate(
    phaseFrame,
    [0, phaseDuration * 0.3, phaseDuration * 0.6, phaseDuration],
    [0, DISSOLUTION_GLOW_OPACITY, DISSOLUTION_GLOW_OPACITY * 0.5, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <div style={{ position: 'absolute', inset: 0 }}>
      {/* Radial glow behind dissolution */}
      <div
        style={{
          position: 'absolute',
          inset: 0,
          background: `radial-gradient(ellipse at 50% 40%, ${DISSOLUTION_GLOW_COLOR} 0%, transparent 70%)`,
          opacity: glowOpacity,
          pointerEvents: 'none',
        }}
      />

      {/* Particles */}
      <svg
        width="1920"
        height="1080"
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', inset: 0 }}
      >
        {particles.map((p, i) => {
          const localFrame = phaseFrame - p.startFrame;
          if (localFrame < 0) {
            // Not yet dissolved — render in original position as a static rect
            return (
              <rect
                key={i}
                x={p.x}
                y={p.y}
                width={DISSOLUTION_PARTICLE_SIZE}
                height={DISSOLUTION_PARTICLE_SIZE}
                fill={p.color}
              />
            );
          }

          // Particle has started dissolving
          const driftProgress = Math.min(localFrame / DISSOLUTION_FADE_DURATION, 1);

          // Easing for drift: easeOut cubic
          const easedDrift = interpolate(
            driftProgress,
            [0, 1],
            [0, 1],
            { easing: Easing.out(Easing.cubic) }
          );

          const dx = p.vx * localFrame * easedDrift;
          const dy = p.vy * localFrame * easedDrift;

          // Fade: linear over fadeDuration
          const opacity = interpolate(
            localFrame,
            [0, DISSOLUTION_FADE_DURATION],
            [1, 0],
            { extrapolateRight: 'clamp' }
          );

          if (opacity <= 0) return null;

          return (
            <rect
              key={i}
              x={p.x + dx}
              y={p.y + dy}
              width={DISSOLUTION_PARTICLE_SIZE}
              height={DISSOLUTION_PARTICLE_SIZE}
              fill={p.color}
              opacity={opacity}
            />
          );
        })}
      </svg>
    </div>
  );
};
