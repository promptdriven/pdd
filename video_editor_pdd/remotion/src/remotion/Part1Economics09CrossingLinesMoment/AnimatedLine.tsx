import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import { xToPixel, yToPixel } from "./constants";

interface DataPoint {
  x: number;
  y: number;
}

interface AnimatedLineProps {
  data: DataPoint[];
  color: string;
  strokeWidth?: number;
  dashed?: boolean;
  dashArray?: string;
  opacity?: number;
  /** Frame at which this line starts drawing */
  drawStart: number;
  /** How many frames the draw takes */
  drawDuration: number;
  /** Optional pulse after complete draw */
  pulseAfterFrame?: number;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  strokeWidth = 2,
  dashed = false,
  dashArray = "6 4",
  opacity = 1,
  drawStart,
  drawDuration,
  pulseAfterFrame,
}) => {
  const frame = useCurrentFrame();

  if (data.length < 2) return null;

  // Build SVG path
  const points = data.map((d) => ({ px: xToPixel(d.x), py: yToPixel(d.y) }));
  const pathD = points
    .map((p, i) => `${i === 0 ? "M" : "L"} ${p.px} ${p.py}`)
    .join(" ");

  // Compute total length (approximation for strokeDashoffset)
  let totalLength = 0;
  for (let i = 1; i < points.length; i++) {
    const dx = points[i].px - points[i - 1].px;
    const dy = points[i].py - points[i - 1].py;
    totalLength += Math.sqrt(dx * dx + dy * dy);
  }

  const drawProgress = interpolate(
    frame,
    [drawStart, drawStart + drawDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const dashOffset = totalLength * (1 - drawProgress);

  // Pulse effect
  let pulseOpacity = opacity;
  if (pulseAfterFrame !== undefined && frame >= pulseAfterFrame) {
    const pulsePhase = (frame - pulseAfterFrame) % 50;
    const pulseMod = interpolate(
      pulsePhase,
      [0, 25, 50],
      [0, 0.15, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    pulseOpacity = opacity + pulseMod;
  }

  // Visibility
  if (frame < drawStart) return null;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={dashed ? dashArray : `${totalLength}`}
        strokeDashoffset={dashed ? 0 : dashOffset}
        opacity={pulseOpacity}
        style={
          dashed
            ? {
                strokeDasharray: dashArray,
                strokeDashoffset: dashOffset > totalLength * 0.01 ? totalLength : 0,
                opacity: drawProgress > 0.01 ? pulseOpacity : 0,
              }
            : undefined
        }
      />
    </svg>
  );
};

export default AnimatedLine;
