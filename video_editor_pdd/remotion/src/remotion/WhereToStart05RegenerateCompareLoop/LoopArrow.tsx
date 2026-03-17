import React from "react";
import { interpolate, Easing } from "remotion";
import { AMBER } from "./constants";

/**
 * Curved dashed arrow from Step 4 back to Step 2, arcing above the pipeline.
 * Includes "iterate" label at the apex.
 */
export const LoopArrow: React.FC<{ frame: number }> = ({ frame }) => {
  // Draw progress over 20 frames with easeInOut cubic
  const drawProgress = interpolate(frame, [0, 20], [0, 1], {
    easing: Easing.inOut(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Label fades in over 10 frames starting at frame 5
  const labelOpacity = interpolate(frame, [5, 15], [0, 0.4], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Arc path from (1220, 380) to (540, 380), arcing upward
  // Using a quadratic bezier with control point at midpoint, raised
  const startX = 1220;
  const startY = 380;
  const endX = 540;
  const endY = 380;
  const cpX = (startX + endX) / 2; // 880
  const cpY = 280; // arc height (100px above)

  const path = `M ${startX} ${startY} Q ${cpX} ${cpY} ${endX} ${endY}`;

  // Arrowhead at the end point — pointing left and slightly down
  const arrowPath = `M ${endX + 10} ${endY - 5} L ${endX} ${endY} L ${endX + 10} ${endY + 5}`;

  // Total path length estimate for dash offset animation
  const pathLength = 800;

  return (
    <div style={{ position: "absolute", top: 0, left: 0, width: "100%", height: "100%" }}>
      <svg
        width="1920"
        height="1080"
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Dashed arc */}
        <path
          d={path}
          fill="none"
          stroke={AMBER}
          strokeWidth={1.5}
          strokeOpacity={0.3}
          strokeDasharray="4 4"
          strokeDashoffset={pathLength * (1 - drawProgress)}
          style={{ transition: "none" }}
        />
        {/* Arrow head */}
        {drawProgress > 0.9 && (
          <path
            d={arrowPath}
            fill="none"
            stroke={AMBER}
            strokeWidth={1.5}
            strokeOpacity={0.3 * Math.min(1, (drawProgress - 0.9) * 10)}
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        )}
      </svg>

      {/* "iterate" label at apex */}
      <div
        style={{
          position: "absolute",
          left: cpX,
          top: cpY - 20,
          transform: "translateX(-50%)",
          fontFamily: "Inter, sans-serif",
          fontSize: 9,
          color: AMBER,
          opacity: labelOpacity,
          letterSpacing: 0.5,
        }}
      >
        iterate
      </div>
    </div>
  );
};
