import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { LOOP_ARROW_START_FRAME, COLORS } from "./constants";

/**
 * Curved dashed arrow from step 4 back to step 2,
 * arcing above the pipeline to indicate the iteration loop.
 */
export const LoopArrow: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame - LOOP_ARROW_START_FRAME;

  if (localFrame < 0) return null;

  // Draw progress — easeInOut cubic over 20 frames
  const drawProgress = interpolate(localFrame, [0, 20], [0, 1], {
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  // Label fade
  const labelOpacity = interpolate(localFrame, [10, 20], [0, 0.4], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Arc from step 4 (x:1220) back to step 2 (x:540), arcing above at y:380
  // Control point at the apex
  const fromX = 1220;
  const toX = 540;
  const y = 380;
  const apexY = y - 100; // 100px above
  const midX = (fromX + toX) / 2;

  const pathD = `M ${fromX} ${y} Q ${midX} ${apexY} ${toX} ${y}`;

  // Approximate path length for dash animation
  const pathLength = 800;
  const visibleLength = pathLength * drawProgress;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Dashed arc */}
      <path
        d={pathD}
        fill="none"
        stroke={COLORS.amber}
        strokeWidth={1.5}
        strokeOpacity={0.3}
        strokeDasharray="4 4"
        strokeDashoffset={pathLength - visibleLength}
        style={{
          // Use the total path as the "visible" dash segment
          strokeDasharray: `${visibleLength} ${pathLength}`,
        }}
      />

      {/* Arrow head at the end (step 2) */}
      {drawProgress > 0.9 && (
        <polygon
          points={`${toX},${y} ${toX + 6},${y - 5} ${toX + 6},${y + 5}`}
          fill={COLORS.amber}
          fillOpacity={0.3 * Math.min(1, (drawProgress - 0.9) * 10)}
        />
      )}

      {/* "iterate" label at apex */}
      <text
        x={midX}
        y={apexY - 10}
        textAnchor="middle"
        fontSize={14}
        fontFamily="Inter, sans-serif"
        fill={COLORS.amber}
        fillOpacity={labelOpacity}
      >
        iterate
      </text>
    </svg>
  );
};
