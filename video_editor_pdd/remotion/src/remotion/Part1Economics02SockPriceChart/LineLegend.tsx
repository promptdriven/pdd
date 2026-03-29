import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  LABOR_LINE_COLOR,
  GARMENT_LINE_COLOR,
  FONT_FAMILY,
  AXIS_FONT_SIZE,
  CHART_RIGHT,
  CHART_TOP,
  LINE_DRAW_START,
  MORPH_START,
  MORPH_END,
} from "./constants";

/**
 * A small legend in the top-right showing which line is which.
 */
export const LineLegend: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(frame, [LINE_DRAW_START, LINE_DRAW_START + 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const morphFade = interpolate(frame, [MORPH_START, MORPH_END], [1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const opacity = fadeIn * morphFade;

  const legendX = CHART_RIGHT - 200;
  const legendY = CHART_TOP + 20;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <g opacity={opacity}>
        {/* Labor cost legend */}
        <line
          x1={legendX}
          y1={legendY}
          x2={legendX + 28}
          y2={legendY}
          stroke={LABOR_LINE_COLOR}
          strokeWidth={3}
          strokeLinecap="round"
        />
        <text
          x={legendX + 36}
          y={legendY + 5}
          fill={LABOR_LINE_COLOR}
          fontFamily={FONT_FAMILY}
          fontSize={AXIS_FONT_SIZE}
          fontWeight={400}
          opacity={0.85}
        >
          Labor cost
        </text>

        {/* Garment cost legend */}
        <line
          x1={legendX}
          y1={legendY + 28}
          x2={legendX + 28}
          y2={legendY + 28}
          stroke={GARMENT_LINE_COLOR}
          strokeWidth={3}
          strokeLinecap="round"
        />
        <text
          x={legendX + 36}
          y={legendY + 33}
          fill={GARMENT_LINE_COLOR}
          fontFamily={FONT_FAMILY}
          fontSize={AXIS_FONT_SIZE}
          fontWeight={400}
          opacity={0.85}
        >
          Garment cost
        </text>
      </g>
    </svg>
  );
};

export default LineLegend;
