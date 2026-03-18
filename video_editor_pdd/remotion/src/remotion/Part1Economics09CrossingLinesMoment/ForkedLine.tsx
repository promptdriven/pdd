import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  xToPixel,
  yToPixel,
  AMBER_SOLID,
  GREEN_SMALL,
  RED_LARGE,
  SMALL_CODEBASE_DATA,
  LARGE_CODEBASE_DATA,
  PHASE_FORK,
} from "./constants";

/**
 * Draws the forked patch-cost line:
 * - At 2020 the solid amber line forks into two branches
 * - Lower fork (green): small codebase, drops to ~1h
 * - Upper fork (red): large codebase, stays flat ~10-12h
 * - Fork point circle and labels
 */
export const ForkedLine: React.FC = () => {
  const frame = useCurrentFrame();

  const forkStart = PHASE_FORK.start;
  const forkDuration = 40;

  // Lower fork progress
  const lowerProgress = interpolate(
    frame,
    [forkStart, forkStart + forkDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Upper fork progress (starts slightly after)
  const upperProgress = interpolate(
    frame,
    [forkStart + 20, forkStart + 20 + forkDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Label fade
  const labelOpacity = interpolate(
    frame,
    [forkStart + forkDuration, forkStart + forkDuration + 15],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame < forkStart) return null;

  // Build paths
  const buildPath = (data: { x: number; y: number }[]) => {
    const pts = data.map((d) => ({ px: xToPixel(d.x), py: yToPixel(d.y) }));
    return pts.map((p, i) => `${i === 0 ? "M" : "L"} ${p.px} ${p.py}`).join(" ");
  };

  const pathLength = (data: { x: number; y: number }[]) => {
    const pts = data.map((d) => ({ px: xToPixel(d.x), py: yToPixel(d.y) }));
    let len = 0;
    for (let i = 1; i < pts.length; i++) {
      const dx = pts[i].px - pts[i - 1].px;
      const dy = pts[i].py - pts[i - 1].py;
      len += Math.sqrt(dx * dx + dy * dy);
    }
    return len;
  };

  const lowerPath = buildPath(SMALL_CODEBASE_DATA);
  const upperPath = buildPath(LARGE_CODEBASE_DATA);
  const lowerLen = pathLength(SMALL_CODEBASE_DATA);
  const upperLen = pathLength(LARGE_CODEBASE_DATA);

  // Fork point
  const forkPx = xToPixel(2020);
  const forkPy = yToPixel(7);

  // Label positions — at end of each fork
  const lowerEnd = SMALL_CODEBASE_DATA[SMALL_CODEBASE_DATA.length - 1];
  const upperEnd = LARGE_CODEBASE_DATA[LARGE_CODEBASE_DATA.length - 1];

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Lower fork — green / small codebase */}
      <path
        d={lowerPath}
        fill="none"
        stroke={GREEN_SMALL}
        strokeWidth={2}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={lowerLen}
        strokeDashoffset={lowerLen * (1 - lowerProgress)}
      />

      {/* Upper fork — red / large codebase */}
      <path
        d={upperPath}
        fill="none"
        stroke={RED_LARGE}
        strokeWidth={2}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={upperLen}
        strokeDashoffset={upperLen * (1 - upperProgress)}
      />

      {/* Fork point circle */}
      <circle
        cx={forkPx}
        cy={forkPy}
        r={4}
        fill={AMBER_SOLID}
        opacity={0.5}
      />

      {/* Labels */}
      <text
        x={xToPixel(lowerEnd.x) + 10}
        y={yToPixel(lowerEnd.y) + 4}
        fill={GREEN_SMALL}
        fontSize={11}
        fontFamily="Inter, sans-serif"
        opacity={labelOpacity}
      >
        Small codebase
      </text>

      <text
        x={xToPixel(upperEnd.x) + 10}
        y={yToPixel(upperEnd.y) + 4}
        fill={RED_LARGE}
        fontSize={11}
        fontFamily="Inter, sans-serif"
        opacity={labelOpacity}
      >
        Large codebase
      </text>
    </svg>
  );
};

export default ForkedLine;
