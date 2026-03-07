import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BAR_DATA,
  TIMELINE_Y,
  MILESTONES,
  WHITE,
  TEST_GREEN,
  SLATE_400,
} from "./constants";

/**
 * Renders milestone generation labels with arrow connectors
 * pointing to the corresponding bar on the timeline.
 */
export const MilestoneLabels: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {MILESTONES.map((milestone) => {
          const opacity = interpolate(
            frame,
            [milestone.fadeStart, milestone.fadeEnd],
            [0, 1],
            {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
              easing: Easing.out(Easing.cubic),
            }
          );

          if (opacity <= 0) return null;

          const bar = BAR_DATA[Math.min(milestone.barIndex, BAR_DATA.length - 1)];
          const barX = bar.x;
          const barTopY = TIMELINE_Y - bar.cumulativeMax;

          // Label positioned above the bar with some offset
          const labelY = barTopY - 50;
          const arrowStartY = labelY + 8;
          const arrowEndY = barTopY - 6;

          return (
            <g key={milestone.label} opacity={opacity}>
              {/* Arrow connector line */}
              <line
                x1={barX}
                y1={arrowStartY}
                x2={barX}
                y2={arrowEndY}
                stroke={SLATE_400}
                strokeWidth={1}
              />
              {/* Arrow tip */}
              <polygon
                points={`${barX - 3},${arrowEndY - 4} ${barX + 3},${arrowEndY - 4} ${barX},${arrowEndY}`}
                fill={SLATE_400}
              />

              {/* Label text — generation name */}
              <text
                x={barX}
                y={labelY - 18}
                fill={WHITE}
                fontSize={16}
                fontFamily="Inter, sans-serif"
                fontWeight={600}
                textAnchor="middle"
              >
                {milestone.label}
              </text>

              {/* Label text — test count (in green) */}
              <text
                x={barX}
                y={labelY}
                fill={TEST_GREEN}
                fontSize={16}
                fontFamily="Inter, sans-serif"
                fontWeight={700}
                textAnchor="middle"
              >
                {milestone.countLabel}
              </text>
            </g>
          );
        })}
      </svg>
    </AbsoluteFill>
  );
};

export default MilestoneLabels;
