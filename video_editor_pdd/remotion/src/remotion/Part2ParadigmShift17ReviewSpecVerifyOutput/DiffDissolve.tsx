import React, { useMemo } from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';

interface DiffDissolveProps {
  lines: string[];
  dissolveEnd: number;
}

/**
 * Shows a code-diff snapshot that dissolves into particles during
 * frames 0 → dissolveEnd. Visible from frame 0.
 */
const DiffDissolve: React.FC<DiffDissolveProps> = ({ lines, dissolveEnd }) => {
  const frame = useCurrentFrame();

  // Dissolve progress 0→1
  const dissolve = interpolate(frame, [0, dissolveEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  // Overall opacity: fully visible at start, gone at dissolveEnd
  const opacity = interpolate(dissolve, [0, 0.8, 1], [1, 0.4, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Generate pseudo-random particle offsets per character (deterministic)
  const particles = useMemo(() => {
    const result: { dx: number; dy: number; rot: number }[] = [];
    let seed = 42;
    const next = () => {
      seed = (seed * 16807 + 0) % 2147483647;
      return (seed / 2147483647) * 2 - 1; // -1..1
    };
    for (let i = 0; i < 300; i++) {
      result.push({
        dx: next() * 600,
        dy: next() * 400,
        rot: next() * 180,
      });
    }
    return result;
  }, []);

  if (frame >= dissolveEnd + 5) return null;

  return (
    <AbsoluteFill
      style={{
        opacity,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
      }}
    >
      <div
        style={{
          width: 1400,
          fontFamily: '"JetBrains Mono", monospace',
          fontSize: 13,
          lineHeight: '22px',
          padding: 40,
        }}
      >
        {lines.map((line, lineIdx) => {
          const isAdd = line.startsWith('+');
          const isRemove = line.startsWith('-');
          const color = isAdd ? '#4ADE80' : isRemove ? '#F87171' : '#94A3B8';

          return (
            <div key={lineIdx} style={{ display: 'flex', whiteSpace: 'pre' }}>
              {line.split('').map((char, charIdx) => {
                const pIdx = (lineIdx * 50 + charIdx) % particles.length;
                const p = particles[pIdx];
                const tx = p.dx * dissolve;
                const ty = p.dy * dissolve;
                const rot = p.rot * dissolve;
                const charOpacity = interpolate(
                  dissolve,
                  [0, 0.3 + (pIdx % 10) * 0.05, 0.7 + (pIdx % 10) * 0.03],
                  [1, 1, 0],
                  { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
                );

                return (
                  <span
                    key={charIdx}
                    style={{
                      color,
                      display: 'inline-block',
                      transform: `translate(${tx}px, ${ty}px) rotate(${rot}deg)`,
                      opacity: charOpacity,
                    }}
                  >
                    {char === ' ' ? '\u00A0' : char}
                  </span>
                );
              })}
            </div>
          );
        })}
      </div>
    </AbsoluteFill>
  );
};

export default DiffDissolve;
