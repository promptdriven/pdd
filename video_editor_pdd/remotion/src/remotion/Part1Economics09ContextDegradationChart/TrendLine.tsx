import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { WIDTH, HEIGHT, TREND_LINE_COLOR } from "./constants";

interface Point {
  x: number;
  y: number;
}

interface TrendLineProps {
  points: Point[];
  drawStartFrame: number;
  drawEndFrame: number;
}

export const TrendLine: React.FC<TrendLineProps> = ({
  points,
  drawStartFrame,
  drawEndFrame,
}) => {
  const frame = useCurrentFrame();

  const pathD = useMemo(() => {
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

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Use strokeDashoffset to progressively reveal a clip path,
            then clip the dashed trend line through it */}
        <defs>
          <clipPath id="trendDrawClip">
            <path
              d={pathD}
              fill="none"
              stroke="white"
              strokeWidth={20}
              strokeDasharray={`${pathLength} ${pathLength}`}
              strokeDashoffset={pathLength * (1 - drawProgress)}
            />
          </clipPath>
        </defs>

        {/* Dashed trend line, revealed progressively by clip */}
        <path
          d={pathD}
          fill="none"
          stroke={TREND_LINE_COLOR}
          strokeWidth={3}
          strokeOpacity={0.6}
          strokeDasharray="8 6"
          strokeLinecap="round"
          strokeLinejoin="round"
          clipPath="url(#trendDrawClip)"
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
              fill={TREND_LINE_COLOR}
              opacity={dotOpacity}
            />
          );
        })}
      </svg>
    </AbsoluteFill>
  );
};

export default TrendLine;
