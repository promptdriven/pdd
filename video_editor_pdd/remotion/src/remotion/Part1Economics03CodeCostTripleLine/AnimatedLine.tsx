import React, { useMemo } from "react";
import { interpolate, useCurrentFrame } from "remotion";
import {
  CHART_W,
  CHART_H,
  MARGIN,
  buildPathD,
  xToPixel,
  yToPixel,
} from "./constants";
import type { DataPoint } from "./constants";

interface AnimatedLineProps {
  data: DataPoint[];
  color: string;
  strokeWidth: number;
  label: string;
  labelOpacity?: number;
  startFrame: number;
  drawDuration: number;
  dashArray?: string;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  strokeWidth,
  label,
  labelOpacity = 0.7,
  startFrame,
  drawDuration,
  dashArray,
}) => {
  const frame = useCurrentFrame();

  const pathD = useMemo(() => buildPathD(data), [data]);

  // Approximate total path length for stroke-dashoffset animation
  const totalLength = useMemo(() => {
    let len = 0;
    for (let i = 1; i < data.length; i++) {
      const dx = xToPixel(data[i].x) - xToPixel(data[i - 1].x);
      const dy = yToPixel(data[i].y) - yToPixel(data[i - 1].y);
      len += Math.sqrt(dx * dx + dy * dy);
    }
    return len;
  }, [data]);

  // Progress: 0 → 1 over drawDuration, linear
  const progress = interpolate(
    frame,
    [startFrame, startFrame + drawDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Label fade-in near end of draw
  const labelFade = interpolate(
    frame,
    [startFrame + drawDuration - 20, startFrame + drawDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const hiddenLength = totalLength * (1 - progress);

  // Position label at the last data point
  const lastPt = data[data.length - 1];
  const labelX = xToPixel(lastPt.x) + 12;
  const labelY = yToPixel(lastPt.y) + 4;

  // Unique clip ID for this line
  const clipId = `clip-${label.replace(/[\s/()]+/g, "-")}`;

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
        {dashArray ? (
          <>
            {/* Dashed lines use a clip rect to progressively reveal */}
            <defs>
              <clipPath id={clipId}>
                <rect
                  x={0}
                  y={0}
                  width={CHART_W * progress}
                  height={CHART_H}
                />
              </clipPath>
            </defs>
            <path
              d={pathD}
              fill="none"
              stroke={color}
              strokeWidth={strokeWidth}
              strokeLinecap="round"
              strokeLinejoin="round"
              strokeDasharray={dashArray}
              clipPath={`url(#${clipId})`}
            />
          </>
        ) : (
          /* Solid lines use stroke-dashoffset for smooth draw */
          <path
            d={pathD}
            fill="none"
            stroke={color}
            strokeWidth={strokeWidth}
            strokeLinecap="round"
            strokeLinejoin="round"
            strokeDasharray={`${totalLength}`}
            strokeDashoffset={hiddenLength}
          />
        )}

        {/* Line label */}
        <text
          x={labelX}
          y={labelY}
          fill={color}
          fillOpacity={labelOpacity * labelFade}
          fontFamily="Inter, sans-serif"
          fontSize={12}
        >
          {label}
        </text>
      </svg>
    </div>
  );
};
