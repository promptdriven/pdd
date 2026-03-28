import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { WIDTH, HEIGHT, TREND_LINE_COLOR } from "./constants";

interface Point {
  x: number;
  y: number;
}

interface TrendLineProps {
  points: Point[];
  startFrame: number;
  endFrame: number;
}

export const TrendLine: React.FC<TrendLineProps> = ({
  points,
  startFrame,
  endFrame,
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

  if (frame < startFrame) return null;

  const drawProgress = interpolate(frame, [startFrame, endFrame], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
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
      </svg>
    </AbsoluteFill>
  );
};

export default TrendLine;
