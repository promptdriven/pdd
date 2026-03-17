import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  FONT_FAMILY,
  BLUE_LINE_COLOR,
  BLUE_STROKE_WIDTH,
  CROSSING_LINE_START,
  CROSSING_LINE_DRAW,
  WE_ARE_HERE_START,
  PROMPT_ANNOTATION_START,
  GLOW_PULSE_CYCLE,
  GENERATE_CROSSING_DATA,
  dataToPixelX,
  dataToPixelY,
} from "./constants";

interface DataPoint {
  x: number;
  y: number;
}

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
 * CrossingPoint: Renders the blue "generate" line extending and pulsing
 * as it crosses below both amber lines, plus the "We are here." label
 * and crossing dot with glow.
 */
export const CrossingPoint: React.FC = () => {
  const frame = useCurrentFrame();

  const path = useMemo(
    () => dataToSmoothPath(GENERATE_CROSSING_DATA),
    []
  );
  const pathLength = useMemo(
    () => estimatePathLength(GENERATE_CROSSING_DATA),
    []
  );

  // The blue line "pulses" — it re-draws with emphasis to show the crossing
  const drawEnd = CROSSING_LINE_START + CROSSING_LINE_DRAW;

  // Blue line pulse: opacity modulation during draw
  const pulseBase = interpolate(
    frame,
    [CROSSING_LINE_START, CROSSING_LINE_START + 15],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // After the crossing, pulse glow on a cycle
  const glowPulse =
    frame >= WE_ARE_HERE_START
      ? 0.15 +
        0.05 *
          Math.sin(
            ((frame - WE_ARE_HERE_START) / GLOW_PULSE_CYCLE) * Math.PI * 2
          )
      : 0.2;

  // "We are here" crossing point position
  // The generate line is at y=4 at x=2025, crossing below patch cost (~2h)
  // The second crossing (below solid amber) happens around 2024 at ~6h vs ~3h patch
  // Use a point around 2024.5 where blue (~5) is below amber patch (~2.5)
  const crossingX = dataToPixelX(2024.5);
  const crossingY = dataToPixelY(5);

  // "We are here" label appearance
  const weAreHereOpacity = interpolate(
    frame,
    [WE_ARE_HERE_START, WE_ARE_HERE_START + 15],
    [0, 0.85],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Glowing dot size pulse
  const dotPulse =
    frame >= WE_ARE_HERE_START
      ? 10 +
        3 *
          Math.sin(
            ((frame - WE_ARE_HERE_START) / GLOW_PULSE_CYCLE) * Math.PI * 2
          )
      : 10;

  // Prompt annotation
  const promptOpacity = interpolate(
    frame,
    [PROMPT_ANNOTATION_START, PROMPT_ANNOTATION_START + 15],
    [0, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame < CROSSING_LINE_START) return null;

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <filter id="glow-crossing">
            <feGaussianBlur stdDeviation="8" />
          </filter>
          <filter id="glow-dot">
            <feGaussianBlur stdDeviation="10" />
          </filter>
        </defs>

        {/* Enhanced glow layer for the blue line */}
        <path
          d={path}
          fill="none"
          stroke={BLUE_LINE_COLOR}
          strokeWidth={BLUE_STROKE_WIDTH * 4}
          strokeLinecap="round"
          strokeLinejoin="round"
          opacity={pulseBase * glowPulse}
          filter="url(#glow-crossing)"
        />

        {/* Re-drawn blue line with emphasis */}
        <path
          d={path}
          fill="none"
          stroke={BLUE_LINE_COLOR}
          strokeWidth={BLUE_STROKE_WIDTH}
          strokeLinecap="round"
          strokeLinejoin="round"
          opacity={pulseBase}
        />

        {/* "We are here" glowing dot */}
        {frame >= WE_ARE_HERE_START && (
          <>
            {/* Outer glow */}
            <circle
              cx={crossingX}
              cy={crossingY}
              r={20}
              fill={BLUE_LINE_COLOR}
              opacity={weAreHereOpacity * 0.2}
              filter="url(#glow-dot)"
            />
            {/* Inner dot */}
            <circle
              cx={crossingX}
              cy={crossingY}
              r={dotPulse / 2}
              fill={BLUE_LINE_COLOR}
              opacity={weAreHereOpacity}
            />

            {/* "We are here." label */}
            <text
              x={crossingX - 80}
              y={crossingY - 24}
              fill={BLUE_LINE_COLOR}
              fontSize={16}
              fontFamily={FONT_FAMILY}
              fontWeight={700}
              opacity={weAreHereOpacity}
            >
              We are here.
            </text>
          </>
        )}

        {/* Small prompt annotation */}
        {frame >= PROMPT_ANNOTATION_START && (
          <text
            x={crossingX - 80}
            y={crossingY + 28}
            fill={BLUE_LINE_COLOR}
            fontSize={9}
            fontFamily={FONT_FAMILY}
            fontWeight={400}
            opacity={promptOpacity}
          >
            Small modules. Clear prompts. Always fits in context.
          </text>
        )}
      </svg>
    </AbsoluteFill>
  );
};

export default CrossingPoint;
