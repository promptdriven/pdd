import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  FONT_FAMILY,
  AMBER_LINE_COLOR,
  GREEN_FORK_COLOR,
  RED_FORK_COLOR,
  FORK_STROKE_WIDTH,
  FORK_START,
  FORK_DRAW_DURATION,
  dataToPixelX,
  dataToPixelY,
  SMALL_CODEBASE_DATA,
  LARGE_CODEBASE_DATA,
} from "./constants";

interface DataPoint {
  x: number;
  y: number;
}

/** Convert data points to a smooth cubic Bezier SVG path. */
function dataToSmoothPath(data: DataPoint[]): string {
  if (data.length < 2) return "";
  const pts = data.map((d) => ({
    x: dataToPixelX(d.x),
    y: dataToPixelY(d.y),
  }));
  let d = `M ${pts[0].x} ${pts[0].y}`;
  const tension = 0.3;
  for (let i = 0; i < pts.length - 1; i++) {
    const p0 = pts[Math.max(0, i - 1)];
    const p1 = pts[i];
    const p2 = pts[i + 1];
    const p3 = pts[Math.min(pts.length - 1, i + 2)];
    const cp1x = p1.x + (p2.x - p0.x) * tension;
    const cp1y = p1.y + (p2.y - p0.y) * tension;
    const cp2x = p2.x - (p3.x - p1.x) * tension;
    const cp2y = p2.y - (p3.y - p1.y) * tension;
    d += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${p2.x} ${p2.y}`;
  }
  return d;
}

function estimatePathLength(data: DataPoint[]): number {
  const pts = data.map((d) => ({
    x: dataToPixelX(d.x),
    y: dataToPixelY(d.y),
  }));
  let len = 0;
  for (let i = 1; i < pts.length; i++) {
    const dx = pts[i].x - pts[i - 1].x;
    const dy = pts[i].y - pts[i - 1].y;
    len += Math.sqrt(dx * dx + dy * dy);
  }
  return len * 1.2;
}

/**
 * ForkedLine: Renders the amber patch line forking at 2020 into
 * a lower "small codebase" (green) and upper "large codebase" (red) fork.
 */
export const ForkedLine: React.FC = () => {
  const frame = useCurrentFrame();

  const lowerPath = useMemo(
    () => dataToSmoothPath(SMALL_CODEBASE_DATA),
    []
  );
  const upperPath = useMemo(
    () => dataToSmoothPath(LARGE_CODEBASE_DATA),
    []
  );
  const lowerLength = useMemo(
    () => estimatePathLength(SMALL_CODEBASE_DATA),
    []
  );
  const upperLength = useMemo(
    () => estimatePathLength(LARGE_CODEBASE_DATA),
    []
  );

  // Lower fork draws first
  const lowerStart = FORK_START;
  const lowerEnd = lowerStart + FORK_DRAW_DURATION;
  const lowerProgress = interpolate(
    frame,
    [lowerStart, lowerEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Upper fork draws after lower
  const upperStart = lowerEnd;
  const upperEnd = upperStart + FORK_DRAW_DURATION;
  const upperProgress = interpolate(
    frame,
    [upperStart, upperEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Fork point dot
  const forkX = dataToPixelX(2020);
  const forkY = dataToPixelY(7);
  const forkDotOpacity = interpolate(
    frame,
    [FORK_START, FORK_START + 10],
    [0, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Label opacity (appears after line draws)
  const lowerLabelOpacity = interpolate(
    frame,
    [lowerEnd, lowerEnd + 15],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );
  const upperLabelOpacity = interpolate(
    frame,
    [upperEnd, upperEnd + 15],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame < FORK_START) return null;

  const lowerLast = SMALL_CODEBASE_DATA[SMALL_CODEBASE_DATA.length - 1];
  const upperLast = LARGE_CODEBASE_DATA[LARGE_CODEBASE_DATA.length - 1];

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Fork point dot */}
        <circle
          cx={forkX}
          cy={forkY}
          r={4}
          fill={AMBER_LINE_COLOR}
          opacity={forkDotOpacity}
        />

        {/* Lower fork (small codebase — green, plunges) */}
        <path
          d={lowerPath}
          fill="none"
          stroke={GREEN_FORK_COLOR}
          strokeWidth={FORK_STROKE_WIDTH}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={`${lowerLength} ${lowerLength}`}
          strokeDashoffset={lowerLength * (1 - lowerProgress)}
        />

        {/* Lower fork label */}
        <text
          x={dataToPixelX(lowerLast.x) + 14}
          y={dataToPixelY(lowerLast.y) + 4}
          fill={GREEN_FORK_COLOR}
          fontSize={11}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          opacity={lowerLabelOpacity}
        >
          Small codebase
        </text>

        {/* Upper fork (large codebase — red, stays flat) */}
        <path
          d={upperPath}
          fill="none"
          stroke={RED_FORK_COLOR}
          strokeWidth={FORK_STROKE_WIDTH}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={`${upperLength} ${upperLength}`}
          strokeDashoffset={upperLength * (1 - upperProgress)}
        />

        {/* Upper fork label */}
        <text
          x={dataToPixelX(upperLast.x) + 14}
          y={dataToPixelY(upperLast.y) + 4}
          fill={RED_FORK_COLOR}
          fontSize={11}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          opacity={upperLabelOpacity}
        >
          Large codebase
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default ForkedLine;
