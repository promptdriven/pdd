import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CROSSING_YEAR,
  CROSSING_Y,
  xToPixel,
  yToPixel,
  THRESHOLD_LABEL_COLOR,
  THRESHOLD_GLOW_COLOR,
  THRESHOLD_GLOW_OPACITY,
  GLOW_RADIUS,
  FONT_FAMILY,
  THRESHOLD_FONT_SIZE,
  THRESHOLD_LABEL_START,
  THRESHOLD_LABEL_DURATION,
  DARNING_SENSE_COLOR,
  DARNING_IRRATIONAL_COLOR,
  ZONE_LABEL_OPACITY,
  ZONE_FONT_SIZE,
  IRRATIONAL_LABEL_START,
  IRRATIONAL_LABEL_DURATION,
  MORPH_START,
  MORPH_END,
} from "./constants";

/**
 * Renders the crossing-point glow, "The Threshold" label,
 * and the two zone labels ("Darning makes sense" / "Darning is irrational").
 */
export const CrossingHighlight: React.FC = () => {
  const frame = useCurrentFrame();

  const cx = xToPixel(CROSSING_YEAR);
  const cy = yToPixel(CROSSING_Y);

  // ── Crossing flash + glow ──
  // Flash: bright at frame 150, fades to steady glow
  const flashOpacity = interpolate(
    frame,
    [THRESHOLD_LABEL_START, THRESHOLD_LABEL_START + 10, THRESHOLD_LABEL_START + 30],
    [0, 0.6, THRESHOLD_GLOW_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // ── "The Threshold" label animation ──
  const labelProgress = interpolate(
    frame,
    [THRESHOLD_LABEL_START + 5, THRESHOLD_LABEL_START + THRESHOLD_LABEL_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const labelScale = interpolate(labelProgress, [0, 1], [1.05, 1.0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const labelOpacity = interpolate(labelProgress, [0, 0.3], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── "Darning makes sense" label (left of crossing) ──
  // Appears slightly before crossing (when lines are being drawn toward it)
  const senseProgress = interpolate(
    frame,
    [90, 110],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── "Darning is irrational" label (right of crossing) ──
  const irrationalProgress = interpolate(
    frame,
    [IRRATIONAL_LABEL_START, IRRATIONAL_LABEL_START + IRRATIONAL_LABEL_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Morph fade-out ──
  const morphOpacity = interpolate(
    frame,
    [MORPH_START, MORPH_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <defs>
        <radialGradient id="crossing-glow">
          <stop offset="0%" stopColor={THRESHOLD_GLOW_COLOR} stopOpacity={1} />
          <stop offset="100%" stopColor={THRESHOLD_GLOW_COLOR} stopOpacity={0} />
        </radialGradient>
      </defs>

      {/* Radial glow at crossing point */}
      <circle
        cx={cx}
        cy={cy}
        r={GLOW_RADIUS * 2.5}
        fill="url(#crossing-glow)"
        opacity={flashOpacity * morphOpacity}
      />

      {/* Small bright dot at crossing */}
      <circle
        cx={cx}
        cy={cy}
        r={5}
        fill={THRESHOLD_GLOW_COLOR}
        opacity={flashOpacity * morphOpacity * 2}
      />

      {/* "The Threshold" label */}
      <g
        opacity={labelOpacity * morphOpacity}
        transform={`translate(${cx}, ${cy - 45}) scale(${labelScale})`}
      >
        {/* Connecting line from label to point */}
        <line
          x1={0}
          y1={20}
          x2={0}
          y2={35}
          stroke={THRESHOLD_LABEL_COLOR}
          strokeWidth={1}
          opacity={0.5}
        />
        <text
          x={0}
          y={0}
          textAnchor="middle"
          fill={THRESHOLD_LABEL_COLOR}
          fontFamily={FONT_FAMILY}
          fontSize={THRESHOLD_FONT_SIZE}
          fontWeight={700}
        >
          The Threshold
        </text>
      </g>

      {/* "Darning makes sense" — left of crossing */}
      <text
        x={cx - 120}
        y={cy + 60}
        textAnchor="middle"
        fill={DARNING_SENSE_COLOR}
        opacity={senseProgress * ZONE_LABEL_OPACITY * morphOpacity}
        fontFamily={FONT_FAMILY}
        fontSize={ZONE_FONT_SIZE}
        fontWeight={400}
      >
        Darning makes sense
      </text>

      {/* "Darning is irrational" — right of crossing */}
      <text
        x={cx + 200}
        y={cy + 60}
        textAnchor="middle"
        fill={DARNING_IRRATIONAL_COLOR}
        opacity={irrationalProgress * ZONE_LABEL_OPACITY * morphOpacity}
        fontFamily={FONT_FAMILY}
        fontSize={ZONE_FONT_SIZE}
        fontWeight={400}
      >
        Darning is irrational
      </text>
    </svg>
  );
};

export default CrossingHighlight;
