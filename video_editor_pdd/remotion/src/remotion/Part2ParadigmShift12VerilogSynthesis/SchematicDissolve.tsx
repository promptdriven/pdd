import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { SCHEMATIC_COLOR, WIDTH, HEIGHT, DISSOLVE_END } from "./constants";

interface Particle {
  x: number;
  y: number;
  size: number;
  dx: number;
  dy: number;
  rotation: number;
  type: "line" | "circle" | "rect";
}

// Deterministic pseudo-random
function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return (s - 1) / 2147483646;
  };
}

export const SchematicDissolve: React.FC = () => {
  const frame = useCurrentFrame();

  const particles = useMemo<Particle[]>(() => {
    const rand = seededRandom(42);
    const result: Particle[] = [];
    // Generate schematic-like elements (lines, circles, rectangles)
    for (let i = 0; i < 120; i++) {
      result.push({
        x: 300 + rand() * (WIDTH - 600),
        y: 100 + rand() * (HEIGHT - 200),
        size: 4 + rand() * 20,
        dx: (rand() - 0.5) * 8,
        dy: (rand() - 0.5) * 6 + 2,
        rotation: rand() * 360,
        type: i % 3 === 0 ? "circle" : i % 3 === 1 ? "rect" : "line",
      });
    }
    return result;
  }, []);

  const dissolveProgress = interpolate(frame, [0, DISSOLVE_END], [0, 1], {
    easing: Easing.in(Easing.quad),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const opacity = interpolate(frame, [0, DISSOLVE_END], [0.85, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  if (frame >= DISSOLVE_END) return null;

  return (
    <AbsoluteFill style={{ opacity }}>
      <svg width={WIDTH} height={HEIGHT}>
        {particles.map((p, i) => {
          const px = p.x + p.dx * dissolveProgress * 40;
          const py = p.y + p.dy * dissolveProgress * 40;
          const scale = 1 - dissolveProgress * 0.6;
          const rot = p.rotation + dissolveProgress * 180;

          if (p.type === "circle") {
            return (
              <circle
                key={i}
                cx={px}
                cy={py}
                r={p.size * scale * 0.5}
                fill="none"
                stroke={SCHEMATIC_COLOR}
                strokeWidth={1.5}
                opacity={0.7}
                transform={`rotate(${rot} ${px} ${py})`}
              />
            );
          }
          if (p.type === "rect") {
            return (
              <rect
                key={i}
                x={px - p.size * scale * 0.5}
                y={py - p.size * scale * 0.3}
                width={p.size * scale}
                height={p.size * scale * 0.6}
                fill="none"
                stroke={SCHEMATIC_COLOR}
                strokeWidth={1.5}
                opacity={0.7}
                transform={`rotate(${rot} ${px} ${py})`}
              />
            );
          }
          // line
          return (
            <line
              key={i}
              x1={px - p.size * scale * 0.5}
              y1={py}
              x2={px + p.size * scale * 0.5}
              y2={py}
              stroke={SCHEMATIC_COLOR}
              strokeWidth={1.5}
              opacity={0.7}
              transform={`rotate(${rot} ${px} ${py})`}
            />
          );
        })}

        {/* Schematic connecting lines */}
        {particles.slice(0, 40).map((p, i) => {
          const next = particles[(i + 1) % 40];
          const px1 = p.x + p.dx * dissolveProgress * 40;
          const py1 = p.y + p.dy * dissolveProgress * 40;
          const px2 = next.x + next.dx * dissolveProgress * 40;
          const py2 = next.y + next.dy * dissolveProgress * 40;
          const dist = Math.sqrt((px2 - px1) ** 2 + (py2 - py1) ** 2);
          if (dist > 200) return null;
          return (
            <line
              key={`conn-${i}`}
              x1={px1}
              y1={py1}
              x2={px2}
              y2={py2}
              stroke={SCHEMATIC_COLOR}
              strokeWidth={0.8}
              opacity={0.4}
            />
          );
        })}
      </svg>
    </AbsoluteFill>
  );
};
