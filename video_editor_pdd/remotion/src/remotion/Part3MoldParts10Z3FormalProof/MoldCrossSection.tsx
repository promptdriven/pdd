import React from "react";
import { interpolate, useCurrentFrame } from "remotion";

// ── Colors & geometry inlined to avoid cross-file imports ──
const MOLD_BLUE = "#4A90D9";
const PURPLE_ACCENT = "#A78BFA";
const MOLD_WALL_CLR = "#334155";
const MOLD_CAVITY_CLR = "#1E293B";

interface WallSeg {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
}

const WALLS: WallSeg[] = [
  { x1: 200, y1: 300, x2: 200, y2: 700 },
  { x1: 350, y1: 350, x2: 350, y2: 650 },
  { x1: 500, y1: 300, x2: 500, y2: 700 },
  { x1: 650, y1: 350, x2: 650, y2: 650 },
  { x1: 800, y1: 300, x2: 800, y2: 700 },
];

const PROVEN_INDICES = [1, 3];

// Cavity rectangles between walls
const CAVITIES = [
  { x: 200, y: 350, w: 150, h: 300 },
  { x: 350, y: 350, w: 150, h: 300 },
  { x: 500, y: 350, w: 150, h: 300 },
  { x: 650, y: 350, w: 150, h: 300 },
];

// Top & bottom plates
const TOP_PLATE = { x: 150, y: 280, w: 700, h: 20 };
const BOTTOM_PLATE = { x: 150, y: 700, w: 700, h: 20 };

interface MoldCrossSectionProps {
  /** Overall mold opacity (dims when annotation appears) */
  moldOpacity: number;
  /** 0..1 progress for proven wall transition blue→purple */
  provenProgress: number;
  /** Whether proven walls should retain purple tint during slide-out */
  retainPurple: boolean;
}

const MoldCrossSection: React.FC<MoldCrossSectionProps> = ({
  moldOpacity,
  provenProgress,
  retainPurple,
}) => {
  const frame = useCurrentFrame();

  // Subtle pulsing glow for proven walls
  const glowPulse = interpolate(
    frame % 60,
    [0, 30, 60],
    [0.2, 0.45, 0.2],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const wallGlowRadius = interpolate(
    provenProgress,
    [0, 1],
    [0, 12],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
        opacity: moldOpacity,
      }}
    >
      <svg width={1920} height={1080} viewBox="0 0 1920 1080">
        {/* Top plate */}
        <rect
          x={TOP_PLATE.x}
          y={TOP_PLATE.y}
          width={TOP_PLATE.w}
          height={TOP_PLATE.h}
          fill={MOLD_WALL_CLR}
          rx={4}
        />
        {/* Bottom plate */}
        <rect
          x={BOTTOM_PLATE.x}
          y={BOTTOM_PLATE.y}
          width={BOTTOM_PLATE.w}
          height={BOTTOM_PLATE.h}
          fill={MOLD_WALL_CLR}
          rx={4}
        />

        {/* Cavities */}
        {CAVITIES.map((c, i) => (
          <rect
            key={`cavity-${i}`}
            x={c.x}
            y={c.y}
            width={c.w}
            height={c.h}
            fill={MOLD_CAVITY_CLR}
            opacity={0.6}
          />
        ))}

        {/* Glow filters */}
        <defs>
          <filter id="blueGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="6" result="blur" />
            <feFlood floodColor={MOLD_BLUE} floodOpacity="0.3" result="color" />
            <feComposite in="color" in2="blur" operator="in" result="glow" />
            <feMerge>
              <feMergeNode in="glow" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
          <filter id="purpleGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation={wallGlowRadius} result="blur" />
            <feFlood
              floodColor={PURPLE_ACCENT}
              floodOpacity={glowPulse}
              result="color"
            />
            <feComposite in="color" in2="blur" operator="in" result="glow" />
            <feMerge>
              <feMergeNode in="glow" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Walls */}
        {WALLS.map((wall, i) => {
          const isProven = PROVEN_INDICES.includes(i);
          const usesPurple = isProven && (provenProgress > 0 || retainPurple);

          // Interpolate color
          const r = Math.round(
            interpolate(
              usesPurple ? provenProgress : 0,
              [0, 1],
              [74, 167],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            )
          );
          const g = Math.round(
            interpolate(
              usesPurple ? provenProgress : 0,
              [0, 1],
              [144, 139],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            )
          );
          const b = Math.round(
            interpolate(
              usesPurple ? provenProgress : 0,
              [0, 1],
              [217, 250],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            )
          );

          const strokeColor = usesPurple
            ? `rgb(${r},${g},${b})`
            : MOLD_BLUE;

          return (
            <line
              key={`wall-${i}`}
              x1={wall.x1}
              y1={wall.y1}
              x2={wall.x2}
              y2={wall.y2}
              stroke={strokeColor}
              strokeWidth={6}
              strokeLinecap="round"
              filter={
                usesPurple && provenProgress > 0.1
                  ? "url(#purpleGlow)"
                  : "url(#blueGlow)"
              }
            />
          );
        })}

        {/* Small horizontal ribs connecting walls */}
        {[380, 500, 620].map((yy) => (
          <line
            key={`rib-${yy}`}
            x1={200}
            y1={yy}
            x2={800}
            y2={yy}
            stroke={MOLD_WALL_CLR}
            strokeWidth={2}
            opacity={0.35}
          />
        ))}
      </svg>
    </div>
  );
};

export default MoldCrossSection;
