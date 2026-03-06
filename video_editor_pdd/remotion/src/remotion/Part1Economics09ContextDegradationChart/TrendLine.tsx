import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";

const CHART_X = 300;
const CHART_Y = 150;
const CHART_W = 1320;
const CHART_H = 700;
const BAR_WIDTH = 120;
const BAR_GAP = 60;
const NUM_BARS = 5;
const TOTAL_BARS_WIDTH = NUM_BARS * BAR_WIDTH + (NUM_BARS - 1) * BAR_GAP;
const BARS_START_X = CHART_X + (CHART_W - TOTAL_BARS_WIDTH) / 2;

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

  const pathD = useMemo(() => {
    if (points.length < 2) return "";
    return points.map((p, i) => `${i === 0 ? "M" : "L"} ${p.x} ${p.y}`).join(" ");
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
    }
  );

  const dashOffset = pathLength * (1 - drawProgress);

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <path
          d={pathD}
          fill="none"
          stroke="#FFFFFF"
          strokeWidth={3}
          strokeDasharray={`8 6`}
          strokeDashoffset={dashOffset}
          strokeLinecap="round"
          strokeLinejoin="round"
          opacity={0.6}
        />

        {/* Dots at each bar top */}
        {points.map((p, i) => (
          <circle
            key={`trend-dot-${i}`}
            cx={p.x}
            cy={p.y}
            r={5}
            fill="#FFFFFF"
            opacity={0.6 * drawProgress}
          />
        ))}
      </svg>
    </AbsoluteFill>
  );
};

export default TrendLine;
