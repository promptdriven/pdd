import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CHART_W,
  CHART_H,
  MARGIN,
  LABEL_COLOR,
  MILESTONES,
  MILESTONE_START,
  MILESTONE_FADE_DUR,
  xToPixel,
} from "./constants";

export const MilestoneMarkers: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <div
      style={{
        position: "absolute",
        left: MARGIN.left,
        top: MARGIN.top,
        width: CHART_W,
        height: CHART_H,
        pointerEvents: "none",
      }}
    >
      <svg
        width={CHART_W}
        height={CHART_H}
        viewBox={`0 0 ${CHART_W} ${CHART_H}`}
        style={{ overflow: "visible" }}
      >
        {MILESTONES.map((ms, i) => {
          const fadeStart = MILESTONE_START + i * 5;
          const opacity = interpolate(
            frame,
            [fadeStart, fadeStart + MILESTONE_FADE_DUR],
            [0, 1],
            {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
              easing: Easing.out(Easing.quad),
            }
          );

          const px = xToPixel(ms.x);

          return (
            <g key={ms.label} opacity={opacity}>
              {/* Vertical dashed line */}
              <line
                x1={px}
                y1={0}
                x2={px}
                y2={CHART_H}
                stroke={LABEL_COLOR}
                strokeOpacity={0.12}
                strokeWidth={1}
                strokeDasharray="4 3"
              />
              {/* Rotated label at top */}
              <text
                x={px}
                y={-12}
                textAnchor="end"
                fill={LABEL_COLOR}
                fillOpacity={0.3}
                fontFamily="Inter, sans-serif"
                fontSize={9}
                transform={`rotate(-45, ${px}, -12)`}
              >
                {ms.label}
              </text>
            </g>
          );
        })}
      </svg>
    </div>
  );
};
