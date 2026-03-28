import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

const LIQUID_COLOR = '#4A90D9';
const LIQUID_OPACITY = 0.4;

// Mold dimensions (must match MoldCavity)
const CX = 470;
const CY = 310;
const W = 340;
const H = 260;
const WALL_STROKE = 4;

// Cavity bounds
const LEFT = CX - W / 2 + WALL_STROKE;
const RIGHT = CX + W / 2 - WALL_STROKE;
const TOP = CY - H / 2 + WALL_STROKE;
const BOTTOM = CY + H / 2 - WALL_STROKE;

// Injection entry point
const ENTRY_X = CX;
const ENTRY_Y = CY - H / 2 - 20;

// Internal wall positions for collision
const INNER_WALL_LEFT_X = CX - W / 4;
const INNER_WALL_RIGHT_X = CX + W / 4;
const INNER_WALL_MID_Y = CY;

interface Particle {
  id: number;
  startFrame: number;
  startX: number;
  startY: number;
  vx: number;
  vy: number;
  size: number;
  wobblePhase: number;
  wobbleAmp: number;
}

// Seeded pseudo-random
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 12.9898 + seed * 78.233) * 43758.5453;
  return x - Math.floor(x);
}

interface LiquidFlowProps {
  panelWidth: number;
  panelHeight: number;
}

export const LiquidFlow: React.FC<LiquidFlowProps> = ({
  panelWidth,
  panelHeight,
}) => {
  const frame = useCurrentFrame();

  // Generate particles with deterministic randomness
  const particles = useMemo<Particle[]>(() => {
    const pts: Particle[] = [];
    const NUM_PARTICLES = 120;
    for (let i = 0; i < NUM_PARTICLES; i++) {
      const r1 = seededRandom(i * 7 + 1);
      const r2 = seededRandom(i * 7 + 2);
      const r3 = seededRandom(i * 7 + 3);
      const r4 = seededRandom(i * 7 + 4);
      const r5 = seededRandom(i * 7 + 5);

      pts.push({
        id: i,
        startFrame: 30 + Math.floor(r1 * 240), // stagger particle emission
        startX: ENTRY_X + (r2 - 0.5) * 10,
        startY: ENTRY_Y,
        vx: (r3 - 0.5) * 3.0,
        vy: 1.2 + r4 * 2.0,
        size: 3 + r5 * 5,
        wobblePhase: r3 * Math.PI * 2,
        wobbleAmp: 0.5 + r4 * 1.5,
      });
    }
    return pts;
  }, []);

  // Fill level — represents how full the cavity is
  const fillProgress = interpolate(frame, [30, 390], [0, 1], {
    easing: Easing.in(Easing.quad),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Filled region from bottom up
  const fillHeight = fillProgress * (BOTTOM - TOP);
  const fillTop = BOTTOM - fillHeight;

  return (
    <svg
      width={panelWidth}
      height={panelHeight}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Liquid fill — rising from bottom */}
      {fillProgress > 0.01 && (
        <rect
          x={LEFT}
          y={fillTop}
          width={RIGHT - LEFT}
          height={fillHeight}
          fill={LIQUID_COLOR}
          opacity={LIQUID_OPACITY * 0.6}
          rx={2}
        />
      )}

      {/* Stream from injection point to cavity */}
      {frame >= 30 && (
        <line
          x1={ENTRY_X}
          y1={ENTRY_Y}
          x2={ENTRY_X}
          y2={Math.min(TOP + 20, fillTop)}
          stroke={LIQUID_COLOR}
          strokeWidth={4}
          opacity={interpolate(frame, [30, 50], [0, LIQUID_OPACITY * 0.8], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          })}
          strokeLinecap="round"
        />
      )}

      {/* Animated particles */}
      {particles.map((p) => {
        if (frame < p.startFrame) return null;
        const age = frame - p.startFrame;
        const maxAge = 180;
        if (age > maxAge) return null;

        const t = age / maxAge;

        // Initial fast downward flow, then spreading
        let px = p.startX + p.vx * age + Math.sin(age * 0.15 + p.wobblePhase) * p.wobbleAmp * age * 0.05;
        let py = p.startY + p.vy * age * (1 + t * 0.5);

        // Constrain to mold bounds
        px = Math.max(LEFT + 2, Math.min(RIGHT - 2, px));
        py = Math.max(TOP + 2, Math.min(BOTTOM - 2, py));

        // Collision with internal walls — bounce off
        if (px > INNER_WALL_LEFT_X - 3 && px < INNER_WALL_LEFT_X + 3 && py < INNER_WALL_MID_Y + H / 4) {
          px = px < INNER_WALL_LEFT_X ? INNER_WALL_LEFT_X - 4 : INNER_WALL_LEFT_X + 4;
        }
        if (px > INNER_WALL_RIGHT_X - 3 && px < INNER_WALL_RIGHT_X + 3 && py > INNER_WALL_MID_Y - H / 4) {
          px = px < INNER_WALL_RIGHT_X ? INNER_WALL_RIGHT_X - 4 : INNER_WALL_RIGHT_X + 4;
        }

        // Fade in and out
        const opacity = interpolate(t, [0, 0.05, 0.7, 1], [0, LIQUID_OPACITY, LIQUID_OPACITY * 0.8, 0], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        });

        return (
          <circle
            key={`lp-${p.id}`}
            cx={px}
            cy={py}
            r={p.size * (1 - t * 0.3)}
            fill={LIQUID_COLOR}
            opacity={opacity}
          />
        );
      })}
    </svg>
  );
};

export default LiquidFlow;
