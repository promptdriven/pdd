import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  CHART_Y,
  CHART_H,
  BARS_START_X,
  BAR_WIDTH,
  BAR_GAP,
} from "./constants";

interface TrendLineProps {
  capabilities: number[];
  drawStartFrame: number;
  drawEndFrame: number;
}

export const TrendLine: React.FC<TrendLineProps> = ({
  capabilities,
  drawStartFrame,
  drawEndFrame,
}) => {
  const frame = useCurrentFrame();

  // Compute bar top center points
  const points = useMemo(() => {
    return capabilities.map((cap, i) => {
      const barX = BARS_START_X + i * (BAR_WIDTH + BAR_GAP) + BAR_WIDTH / 2;
      const barTopY = CHART_Y + CHART_H * (1 - cap / 100);
      return { x: barX, y: barTopY };
    });
  }, [capabilities]);

  // Solid path for draw-in animation (dashoffset technique)
  const solidPathD = useMemo(() => {
    if (points.length < 2) return "";
    return points
      .map((p, i) => `${i === 0 ? "M" : "L"} ${p.x} ${p.y}`)
      .join(" ");
  }, [points]);

  const pathLength = useMemo(() => {
    let len = 0;
    for (let i = 1; i < points.length; i++) {
      const dx = points[i].x - points[i - 1].x;
      const dy = points[i].y - points[i - 1].y;
      len += Math.sqrt(dx * dx + dy * dy);
    }
    return len;
  }, [points]);

  if (frame < drawStartFrame) return null;

  const drawProgress = interpolate(
    frame,
    [drawStartFrame, drawEndFrame],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    },
  );

  // Use a large dash for the visible portion, gap covers the rest
  const visibleLength = pathLength * drawProgress;
  const dashArray = `${visibleLength} ${pathLength}`;

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Dashed trend line with draw-in via clipPath */}
        <defs>
          <clipPath id="trendLineClip">
            {/* Clip rectangle that grows with draw progress */}
            <rect
              x={points[0]?.x ?? 0}
              y={0}
              width={
                ((points[points.length - 1]?.x ?? 0) - (points[0]?.x ?? 0)) *
                drawProgress
              }
              height={HEIGHT}
            />
          </clipPath>
        </defs>

        {/* Dashed line, revealed progressively by clip */}
        <path
          d={solidPathD}
          fill="none"
          stroke="#FFFFFF"
          strokeWidth={3}
          strokeDasharray="8 6"
          strokeLinecap="round"
          strokeLinejoin="round"
          opacity={0.6}
          clipPath="url(#trendLineClip)"
        />

        {/* Dots at each bar top — fade in as line reaches them */}
        {points.map((p, i) => {
          const pointProgress =
            i === 0 ? 0 : i / (points.length - 1);
          const dotOpacity =
            drawProgress > pointProgress
              ? interpolate(
                  drawProgress,
                  [pointProgress, Math.min(pointProgress + 0.1, 1)],
                  [0, 0.6],
                  {
                    extrapolateLeft: "clamp",
                    extrapolateRight: "clamp",
                  },
                )
              : 0;
          return (
            <circle
              key={`trend-dot-${i}`}
              cx={p.x}
              cy={p.y}
              r={5}
              fill="#FFFFFF"
              opacity={dotOpacity}
            />
          );
        })}
      </svg>
    </AbsoluteFill>
  );
};

export default TrendLine;
