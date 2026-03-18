import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { SCHEMATIC_COLOR, SCHEMATIC_END } from './constants';

/**
 * A hand-drawn schematic that dissolves into particles.
 * Positioned centered at (960, 300), 600x300px.
 */
export const HandDrawnSchematic: React.FC = () => {
  const frame = useCurrentFrame();

  // Dissolve over frames 0-40
  const dissolveProgress = interpolate(frame, [0, SCHEMATIC_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  const opacity = 1 - dissolveProgress;

  // Generate scattered particles for dissolve effect
  const particles = React.useMemo(() => {
    const pts: Array<{ x: number; y: number; dx: number; dy: number; size: number; delay: number }> = [];
    for (let i = 0; i < 60; i++) {
      pts.push({
        x: (i % 10) * 60 + 30,
        y: Math.floor(i / 10) * 50 + 25,
        dx: (Math.sin(i * 1.7) * 80) + 40,
        dy: (Math.cos(i * 2.3) * 60) + 30,
        size: 2 + (i % 3),
        delay: ((i % 10) + Math.floor(i / 10)) * 0.02,
      });
    }
    return pts;
  }, []);

  if (frame >= SCHEMATIC_END + 10) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: 960 - 300,
        top: 300 - 150,
        width: 600,
        height: 300,
      }}
    >
      <svg width={600} height={300} style={{ position: 'absolute', top: 0, left: 0 }}>
        {/* Hand-drawn schematic lines — transistor-like symbols */}
        <g opacity={opacity} stroke={SCHEMATIC_COLOR} strokeWidth={1.5} fill="none" strokeLinecap="round">
          {/* Transistor 1 */}
          <path d="M 80,80 L 80,220" strokeDasharray="4,2" />
          <path d="M 80,120 L 140,120 L 140,100 L 180,120 L 140,140 L 140,120" />
          <path d="M 180,120 L 240,120" />
          <circle cx={80} cy={80} r={4} />

          {/* Transistor 2 */}
          <path d="M 280,60 L 280,180" strokeDasharray="4,2" />
          <path d="M 280,100 L 340,100 L 340,80 L 380,100 L 340,120 L 340,100" />
          <path d="M 380,100 L 440,100" />

          {/* Connecting wires */}
          <path d="M 240,120 L 280,100" />
          <path d="M 440,100 L 520,100 L 520,180" />
          <path d="M 520,180 L 480,180 L 480,220 L 520,220" />

          {/* Ground symbol */}
          <path d="M 80,220 L 120,220" />
          <path d="M 88,228 L 112,228" />
          <path d="M 94,236 L 106,236" />

          {/* VDD label */}
          <text x={75} y={70} fontSize={10} fill={SCHEMATIC_COLOR} opacity={0.5} fontFamily="monospace">
            VDD
          </text>

          {/* More connecting wires for complexity */}
          <path d="M 440,100 L 440,200 L 380,200 L 380,240" />
          <path d="M 180,180 L 240,180 L 240,240" />
          <path d="M 140,200 L 200,200" />

          {/* Additional gate symbols */}
          <path d="M 350,200 C 350,185 380,185 380,200 C 380,215 350,215 350,200" />
          <circle cx={348} cy={200} r={3} />
        </g>

        {/* Dissolving particles */}
        {dissolveProgress > 0 &&
          particles.map((p, i) => {
            const particleDelay = p.delay;
            const pProgress = interpolate(
              dissolveProgress,
              [particleDelay, Math.min(particleDelay + 0.6, 1)],
              [0, 1],
              { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
            );
            return (
              <rect
                key={i}
                x={p.x + p.dx * pProgress}
                y={p.y + p.dy * pProgress}
                width={p.size}
                height={p.size}
                fill={SCHEMATIC_COLOR}
                opacity={Math.max(0, 0.5 * (1 - pProgress))}
                rx={1}
              />
            );
          })}
      </svg>
    </div>
  );
};
