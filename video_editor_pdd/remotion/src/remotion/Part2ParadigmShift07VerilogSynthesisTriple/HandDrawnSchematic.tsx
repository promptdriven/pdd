import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  SCHEMATIC_COLOR,
  SCHEMATIC_OPACITY,
  SCHEMATIC_X,
  SCHEMATIC_Y,
  SCHEMATIC_W,
  SCHEMATIC_H,
  SCHEMATIC_DISSOLVE_START,
  SCHEMATIC_DISSOLVE_END,
} from "./constants";

// Hand-drawn transistor/gate schematic paths (sketchy style)
const SCHEMATIC_PATHS = [
  // Transistor symbol left
  "M -200 -80 L -200 80",
  "M -200 -40 L -150 -40",
  "M -200 0 L -150 0",
  "M -200 40 L -150 40",
  "M -150 -60 L -150 60",
  "M -130 -50 L -130 50",
  // Gate body left
  "M -130 -50 Q -80 0 -130 50",
  "M -80 0 L -40 0",
  // Connecting wires
  "M -40 0 L 0 0",
  "M 0 -30 L 0 30",
  // Transistor symbol right
  "M 40 -80 L 40 80",
  "M 40 -40 L 90 -40",
  "M 40 0 L 90 0",
  "M 40 40 L 90 40",
  "M 90 -60 L 90 60",
  "M 110 -50 L 110 50",
  // Gate body right
  "M 110 -50 Q 160 0 110 50",
  "M 160 0 L 200 0",
  // Horizontal wires top/bottom
  "M -250 -100 L 250 -100",
  "M -250 100 L 250 100",
  // VDD/GND labels (vertical connectors)
  "M 0 -100 L 0 -30",
  "M 0 30 L 0 100",
];

// Generate dissolve particles from the schematic area
const PARTICLE_COUNT = 80;
const particles = Array.from({ length: PARTICLE_COUNT }, (_, i) => {
  const seed = i * 137.508; // golden angle
  return {
    startX: ((seed * 7) % SCHEMATIC_W) - SCHEMATIC_W / 2,
    startY: ((seed * 13) % SCHEMATIC_H) - SCHEMATIC_H / 2,
    endX: ((seed * 7) % SCHEMATIC_W) - SCHEMATIC_W / 2 + (i % 3 === 0 ? 100 : -80) + Math.sin(seed) * 60,
    endY: ((seed * 13) % SCHEMATIC_H) - SCHEMATIC_H / 2 + (i % 2 === 0 ? -120 : 80) + Math.cos(seed) * 40,
    size: 2 + (i % 3),
  };
});

export const HandDrawnSchematic: React.FC = () => {
  const frame = useCurrentFrame();

  const dissolveProgress = interpolate(
    frame,
    [SCHEMATIC_DISSOLVE_START, SCHEMATIC_DISSOLVE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  const schematicOpacity = 1 - dissolveProgress;

  if (frame >= SCHEMATIC_DISSOLVE_END + 10) return null;

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      viewBox={`0 0 ${CANVAS_WIDTH} ${CANVAS_HEIGHT}`}
      style={{ position: "absolute", left: 0, top: 0, pointerEvents: "none" }}
    >
      {/* Schematic lines */}
      <g
        transform={`translate(${SCHEMATIC_X}, ${SCHEMATIC_Y})`}
        opacity={schematicOpacity * SCHEMATIC_OPACITY}
      >
        {SCHEMATIC_PATHS.map((d, i) => (
          <path
            key={`sch-${i}`}
            d={d}
            fill="none"
            stroke={SCHEMATIC_COLOR}
            strokeWidth={1.5}
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        ))}
      </g>

      {/* Dissolve particles */}
      {dissolveProgress > 0 && (
        <g>
          {particles.map((p, i) => {
            const px = interpolate(dissolveProgress, [0, 1], [
              SCHEMATIC_X + p.startX,
              SCHEMATIC_X + p.endX,
            ]);
            const py = interpolate(dissolveProgress, [0, 1], [
              SCHEMATIC_Y + p.startY,
              SCHEMATIC_Y + p.endY,
            ]);
            const particleOpacity = interpolate(
              dissolveProgress,
              [0, 0.3, 1],
              [0, 0.6, 0],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            );
            return (
              <rect
                key={`p-${i}`}
                x={px - p.size / 2}
                y={py - p.size / 2}
                width={p.size}
                height={p.size}
                fill={SCHEMATIC_COLOR}
                opacity={particleOpacity}
              />
            );
          })}
        </g>
      )}
    </svg>
  );
};

export default HandDrawnSchematic;
