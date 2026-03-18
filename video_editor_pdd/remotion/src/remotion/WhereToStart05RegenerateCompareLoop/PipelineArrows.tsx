import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { STEP_POSITIONS, STEPS, COLORS } from "./constants";

/**
 * Draws curved arrows between pipeline steps.
 * Each arrow illuminates when its source step activates.
 */
export const PipelineArrows: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {[0, 1, 2].map((i) => {
        const from = STEP_POSITIONS[i];
        const to = STEP_POSITIONS[i + 1];
        const startFrame = STEPS[i].startFrame;

        // Arrow illumination
        const localFrame = frame - startFrame;
        const illumination = localFrame < 0
          ? 0
          : interpolate(localFrame, [0, 10], [0, 1], {
              extrapolateRight: "clamp",
              easing: Easing.out(Easing.quad),
            });

        // Curve control points
        const midX = (from.x + to.x) / 2;
        const startX = from.x + 40;
        const endX = to.x - 40;
        const y = from.y;

        const dimColor = COLORS.border;
        const litColor = COLORS.blue;
        const currentColor = illumination > 0 ? litColor : dimColor;
        const currentOpacity = interpolate(illumination, [0, 1], [0.3, 0.5]);

        // Draw path with dashoffset animation for "drawing" effect
        const pathD = `M ${startX} ${y} Q ${midX} ${y - 25} ${endX} ${y}`;

        return (
          <g key={i}>
            {/* Arrow line */}
            <path
              d={pathD}
              fill="none"
              stroke={currentColor}
              strokeWidth={1.5}
              strokeOpacity={currentOpacity}
            />
            {/* Arrow head */}
            <polygon
              points={`${endX},${y} ${endX - 6},${y - 4} ${endX - 6},${y + 4}`}
              fill={currentColor}
              fillOpacity={currentOpacity}
            />
          </g>
        );
      })}
    </svg>
  );
};
