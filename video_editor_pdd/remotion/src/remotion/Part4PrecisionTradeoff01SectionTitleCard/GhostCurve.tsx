import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  GHOST_CURVE_COLOR,
  GHOST_CURVE_OPACITY,
  GHOST_GRID_COLOR,
  GHOST_GRID_OPACITY,
  CURVE_DRAW_START,
  CURVE_DRAW_DURATION,
  PULSE_CYCLE_FRAMES,
  FADEOUT_START,
  FADEOUT_DURATION,
  DURATION_FRAMES,
} from "./constants";

/**
 * Renders a faint inverse-hyperbola curve (descending from upper-left to
 * lower-right) with small grid squares scattered along the curve path.
 */
export const GhostCurve: React.FC = () => {
  const frame = useCurrentFrame();

  // Build the inverse-curve path: y = k / (x - x0) shifted to go from
  // upper-left to lower-right across the canvas.
  const pathPoints = useMemo(() => {
    const points: string[] = [];
    const margin = 100;
    const steps = 200;
    for (let i = 0; i <= steps; i++) {
      const t = i / steps;
      const x = margin + t * (WIDTH - 2 * margin);
      // Descending hyperbola: high on the left, low on the right
      const normalizedY = 1 / (0.3 + 2.5 * t);
      const y = 150 + normalizedY * (HEIGHT - 400);
      points.push(`${i === 0 ? "M" : "L"} ${x.toFixed(1)} ${y.toFixed(1)}`);
    }
    return points.join(" ");
  }, []);

  // Approximate total path length for stroke-dashoffset animation
  const approxPathLength = 2400;

  // Draw progress (0 → 1)
  const drawProgress = interpolate(
    frame,
    [CURVE_DRAW_START, CURVE_DRAW_START + CURVE_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Subtle pulse after hold starts
  const pulseOpacity = interpolate(
    frame % PULSE_CYCLE_FRAMES,
    [0, PULSE_CYCLE_FRAMES / 2, PULSE_CYCLE_FRAMES],
    [0, 0.015, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.sin),
    }
  );

  // Final fade-out
  const fadeOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  const dashOffset = approxPathLength * (1 - drawProgress);
  const effectiveOpacity = (GHOST_CURVE_OPACITY + pulseOpacity) * fadeOut;

  // Grid squares along the curve path at intervals
  const gridSquares = useMemo(() => {
    const squares: { x: number; y: number }[] = [];
    const margin = 100;
    const count = 8;
    for (let i = 1; i <= count; i++) {
      const t = i / (count + 1);
      const x = margin + t * (WIDTH - 2 * margin);
      const normalizedY = 1 / (0.3 + 2.5 * t);
      const y = 150 + normalizedY * (HEIGHT - 400);
      squares.push({ x, y });
    }
    return squares;
  }, []);

  return (
    <AbsoluteFill style={{ opacity: fadeOut > 0 ? 1 : 0 }}>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Ghost grid squares along curve */}
        {gridSquares.map((sq, idx) => {
          const sqProgress = interpolate(
            frame,
            [
              CURVE_DRAW_START + idx * 3,
              CURVE_DRAW_START + idx * 3 + CURVE_DRAW_DURATION,
            ],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );
          return (
            <rect
              key={idx}
              x={sq.x - 10}
              y={sq.y - 10}
              width={20}
              height={20}
              fill="none"
              stroke={GHOST_GRID_COLOR}
              strokeWidth={1}
              opacity={GHOST_GRID_OPACITY * sqProgress * fadeOut}
            />
          );
        })}

        {/* Inverse curve */}
        <path
          d={pathPoints}
          fill="none"
          stroke={GHOST_CURVE_COLOR}
          strokeWidth={1.5}
          opacity={effectiveOpacity}
          strokeDasharray={approxPathLength}
          strokeDashoffset={dashOffset}
        />
      </svg>
    </AbsoluteFill>
  );
};

export default GhostCurve;
