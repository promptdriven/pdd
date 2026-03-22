import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

/**
 * Background grid with animated fade-in and subtle floating particles.
 */

interface AnimatedGridProps {
  width: number;
  height: number;
  lineColor: string;
  fadeInEnd: number;
  particleCount: number;
  accentColor: string;
  secondaryAccent: string;
}

export const AnimatedGrid: React.FC<AnimatedGridProps> = ({
  width,
  height,
  lineColor,
  fadeInEnd,
  particleCount,
  accentColor,
  secondaryAccent,
}) => {
  const frame = useCurrentFrame();

  const gridOpacity = interpolate(frame, [0, fadeInEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(3)),
  });

  const gridSpacing = 80;
  const verticalLines = Math.ceil(width / gridSpacing);
  const horizontalLines = Math.ceil(height / gridSpacing);

  // Deterministic particle positions using index-based seeding
  const particles = React.useMemo(() => {
    return Array.from({ length: particleCount }, (_, i) => {
      const seed1 = ((i * 7919 + 104729) % 1000) / 1000;
      const seed2 = ((i * 6271 + 73856) % 1000) / 1000;
      const seed3 = ((i * 4517 + 38447) % 1000) / 1000;
      return {
        x: seed1 * width,
        y: seed2 * height,
        size: 2 + seed3 * 3,
        speed: 0.3 + seed3 * 0.7,
        phase: seed1 * Math.PI * 2,
        useSecondary: i % 3 === 0,
      };
    });
  }, [particleCount, width, height]);

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width,
        height,
        opacity: gridOpacity,
        overflow: "hidden",
      }}
    >
      {/* Grid lines SVG */}
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Vertical lines */}
        {Array.from({ length: verticalLines + 1 }, (_, i) => (
          <line
            key={`v-${i}`}
            x1={i * gridSpacing}
            y1={0}
            x2={i * gridSpacing}
            y2={height}
            stroke={lineColor}
            strokeWidth={1}
          />
        ))}
        {/* Horizontal lines */}
        {Array.from({ length: horizontalLines + 1 }, (_, i) => (
          <line
            key={`h-${i}`}
            x1={0}
            y1={i * gridSpacing}
            x2={width}
            y2={i * gridSpacing}
            stroke={lineColor}
            strokeWidth={1}
          />
        ))}
      </svg>

      {/* Floating particles */}
      {particles.map((p, i) => {
        const yOffset = Math.sin(frame * 0.02 * p.speed + p.phase) * 30;
        const xOffset = Math.cos(frame * 0.015 * p.speed + p.phase) * 20;
        const particleOpacity = interpolate(
          Math.sin(frame * 0.03 + p.phase),
          [-1, 1],
          [0.15, 0.6],
        );
        return (
          <div
            key={i}
            style={{
              position: "absolute",
              left: p.x + xOffset,
              top: p.y + yOffset,
              width: p.size,
              height: p.size,
              borderRadius: "50%",
              backgroundColor: p.useSecondary ? secondaryAccent : accentColor,
              opacity: particleOpacity,
            }}
          />
        );
      })}
    </div>
  );
};

export default AnimatedGrid;
