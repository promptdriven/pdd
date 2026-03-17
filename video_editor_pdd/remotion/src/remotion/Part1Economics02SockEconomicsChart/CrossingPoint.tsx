import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MARGIN_LEFT,
  MARGIN_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  CROSSING_X,
  CROSSING_Y,
  CROSSING_DOT_RADIUS,
  CROSSING_GLOW_RADIUS,
  CROSSING_GLOW_COLOR,
  CROSSING_LABEL_COLOR,
  CROSSING_LABEL_SIZE,
  CROSSING_APPEAR_START,
  CROSSING_LABEL_FADE_START,
  CROSSING_LABEL_FADE_END,
  LABEL_COLOR,
} from "./constants";

const xToPixel = (x: number): number =>
  MARGIN_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

const yToPixel = (y: number): number =>
  MARGIN_TOP + CHART_HEIGHT - ((y - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;

export const CrossingPointMarker: React.FC = () => {
  const frame = useCurrentFrame();

  const cx = xToPixel(CROSSING_X);
  const cy = yToPixel(CROSSING_Y);

  // Dot appearance
  const dotScale = interpolate(
    frame,
    [CROSSING_APPEAR_START, CROSSING_APPEAR_START + 15],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Glow pulse (subtle sine oscillation after appear)
  const glowPhase = frame > CROSSING_APPEAR_START + 15
    ? Math.sin((frame - CROSSING_APPEAR_START - 15) * 0.06) * 0.5 + 0.5
    : 0;
  const glowOpacity = dotScale * (0.1 + 0.05 * glowPhase);

  // Label fade
  const labelOpacity = interpolate(
    frame,
    [CROSSING_LABEL_FADE_START, CROSSING_LABEL_FADE_END],
    [0, 0.85],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Annotation dashed line from label to point
  const annotationOpacity = labelOpacity * 0.3;

  // Label position: above the crossing point
  const labelX = cx;
  const labelY = cy - 50;

  if (frame < CROSSING_APPEAR_START) return null;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Glow */}
      <circle
        cx={cx}
        cy={cy}
        r={CROSSING_GLOW_RADIUS}
        fill={CROSSING_GLOW_COLOR}
        fillOpacity={glowOpacity}
      />

      {/* Dot */}
      <circle
        cx={cx}
        cy={cy}
        r={CROSSING_DOT_RADIUS * dotScale}
        fill={CROSSING_GLOW_COLOR}
        fillOpacity={0.9 * dotScale}
      />

      {/* Annotation dashed line */}
      {labelOpacity > 0 && (
        <line
          x1={labelX}
          y1={labelY + 10}
          x2={cx}
          y2={cy - CROSSING_DOT_RADIUS - 4}
          stroke={CROSSING_LABEL_COLOR}
          strokeOpacity={annotationOpacity}
          strokeWidth={1}
          strokeDasharray="4 3"
        />
      )}

      {/* "The Threshold" label */}
      {labelOpacity > 0 && (
        <text
          x={labelX}
          y={labelY}
          textAnchor="middle"
          fill={CROSSING_LABEL_COLOR}
          fillOpacity={labelOpacity}
          fontSize={CROSSING_LABEL_SIZE}
          fontWeight={700}
          fontFamily="'Inter', sans-serif"
        >
          The Threshold
        </text>
      )}

      {/* Year annotation below crossing */}
      {labelOpacity > 0 && (
        <text
          x={cx}
          y={cy + 28}
          textAnchor="middle"
          fill={LABEL_COLOR}
          fillOpacity={labelOpacity * 0.4}
          fontSize={10}
          fontFamily="'Inter', sans-serif"
        >
          ~{CROSSING_X}
        </text>
      )}
    </svg>
  );
};

export default CrossingPointMarker;
