import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CROSSING_YEAR,
  CROSSING_Y,
  xToPixel,
  yToPixel,
  GLOW_COLOR,
  GLOW_OPACITY,
  GLOW_RADIUS,
  THRESHOLD_LABEL_COLOR,
  THRESHOLD_FONT_SIZE,
  DARNING_SENSE_COLOR,
  DARNING_IRRATIONAL_COLOR,
  FONT_FAMILY,
  ZONE_FONT_SIZE,
  ZONE_LABEL_OPACITY,
  CROSSING_HIGHLIGHT_START,
  CROSSING_HIGHLIGHT_END,
  IRRATIONAL_LABEL_START,
} from "./constants";

/**
 * Renders the crossing point highlight, "The Threshold" label,
 * and zone labels ("Darning makes sense" / "Darning is irrational").
 */
export const CrossingHighlight: React.FC = () => {
  const frame = useCurrentFrame();

  const cx = xToPixel(CROSSING_YEAR);
  const cy = yToPixel(CROSSING_Y);

  // Flash + glow at crossing
  const flashIntensity = interpolate(
    frame,
    [CROSSING_HIGHLIGHT_START, CROSSING_HIGHLIGHT_START + 8, CROSSING_HIGHLIGHT_END],
    [0, 1, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // "The Threshold" label: scale-up with easeOut(back) feel
  // We emulate back easing with a slight overshoot via custom interpolation
  const labelProgress = interpolate(
    frame,
    [CROSSING_HIGHLIGHT_START + 5, CROSSING_HIGHLIGHT_END + 10],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const labelScale = interpolate(
    labelProgress,
    [0, 0.7, 1],
    [0, 1.08, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const labelOpacity = interpolate(
    labelProgress,
    [0, 0.3],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // "Darning makes sense" label — appears with axes, visible from crossing highlight
  const senseOpacity = interpolate(
    frame,
    [CROSSING_HIGHLIGHT_START, CROSSING_HIGHLIGHT_START + 20],
    [0, ZONE_LABEL_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // "Darning is irrational" label — appears after crossing
  const irrationalOpacity = interpolate(
    frame,
    [IRRATIONAL_LABEL_START, IRRATIONAL_LABEL_START + 20],
    [0, ZONE_LABEL_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame < CROSSING_HIGHLIGHT_START) return null;

  return (
    <div style={{ position: "absolute", inset: 0 }}>
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Radial glow at crossing */}
        <defs>
          <radialGradient id="crossing-glow" cx="50%" cy="50%" r="50%">
            <stop offset="0%" stopColor={GLOW_COLOR} stopOpacity={GLOW_OPACITY * flashIntensity * 2} />
            <stop offset="100%" stopColor={GLOW_COLOR} stopOpacity={0} />
          </radialGradient>
        </defs>
        <circle
          cx={cx}
          cy={cy}
          r={GLOW_RADIUS * (1 + flashIntensity * 0.5)}
          fill="url(#crossing-glow)"
        />

        {/* Bright dot at crossing point */}
        <circle
          cx={cx}
          cy={cy}
          r={5}
          fill={GLOW_COLOR}
          opacity={0.7 + flashIntensity * 0.3}
        />

        {/* Connecting line from crossing to label */}
        <line
          x1={cx}
          y1={cy - 10}
          x2={cx}
          y2={cy - 50}
          stroke={THRESHOLD_LABEL_COLOR}
          strokeWidth={1}
          opacity={labelOpacity * 0.5}
          strokeDasharray="3 3"
        />
      </svg>

      {/* "The Threshold" label */}
      <div
        style={{
          position: "absolute",
          left: cx,
          top: cy - 82,
          transform: `translate(-50%, 0) scale(${labelScale})`,
          transformOrigin: "center bottom",
          color: THRESHOLD_LABEL_COLOR,
          fontFamily: FONT_FAMILY,
          fontSize: THRESHOLD_FONT_SIZE,
          fontWeight: 700,
          opacity: labelOpacity,
          whiteSpace: "nowrap",
          textShadow: `0 0 12px rgba(255,255,255,0.2)`,
        }}
      >
        The Threshold
      </div>

      {/* "Darning makes sense" — left of crossing */}
      <div
        style={{
          position: "absolute",
          left: cx - 180,
          top: cy + 30,
          color: DARNING_SENSE_COLOR,
          fontFamily: FONT_FAMILY,
          fontSize: ZONE_FONT_SIZE,
          fontWeight: 400,
          opacity: senseOpacity,
          whiteSpace: "nowrap",
        }}
      >
        Darning makes sense
      </div>

      {/* "Darning is irrational" — right of crossing */}
      <div
        style={{
          position: "absolute",
          left: cx + 40,
          top: cy + 30,
          color: DARNING_IRRATIONAL_COLOR,
          fontFamily: FONT_FAMILY,
          fontSize: ZONE_FONT_SIZE,
          fontWeight: 400,
          opacity: irrationalOpacity,
          whiteSpace: "nowrap",
        }}
      >
        Darning is irrational
      </div>
    </div>
  );
};

export default CrossingHighlight;
