import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  LABEL_TEXT_COLOR,
  LABEL_GLOW_COLOR,
  LABEL_GLOW_OPACITY,
  CONNECTOR_COLOR,
  CONNECTOR_OPACITY,
  FONT_FAMILY,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
} from "./constants";

export interface WeAreHereLabelProps {
  /** Pixel coordinates of the crossing point the connector points to */
  targetX: number;
  targetY: number;
  /** Offset from crossing point where the label sits */
  labelOffsetX?: number;
  labelOffsetY?: number;
}

export const WeAreHereLabel: React.FC<WeAreHereLabelProps> = ({
  targetX,
  targetY,
  labelOffsetX = 60,
  labelOffsetY = 50,
}) => {
  const frame = useCurrentFrame();

  // Fade in over first 30 frames of this component's life
  const fadeIn = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Pulse: gentle opacity oscillation between 0.8 and 1.0 on 60-frame cycle
  const pulsePhase = ((frame - 30) % 60) / 60; // normalize 0..1
  const pulse =
    frame < 30
      ? 1
      : interpolate(
          Math.sin(pulsePhase * Math.PI * 2),
          [-1, 1],
          [0.8, 1.0]
        );

  const labelX = targetX + labelOffsetX;
  const labelY = targetY + labelOffsetY;

  const textOpacity = fadeIn * pulse;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      {/* Connector line from label to crossing point */}
      <line
        x1={labelX}
        y1={labelY - 8}
        x2={targetX}
        y2={targetY}
        stroke={CONNECTOR_COLOR}
        strokeWidth={1.5}
        opacity={fadeIn * CONNECTOR_OPACITY}
      />

      {/* Small circle at crossing point */}
      <circle
        cx={targetX}
        cy={targetY}
        r={4}
        fill={CONNECTOR_COLOR}
        opacity={fadeIn * 0.5}
      />

      {/* Text glow (soft background) */}
      <text
        x={labelX}
        y={labelY + LABEL_FONT_SIZE / 3}
        textAnchor="start"
        fill={LABEL_GLOW_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={LABEL_FONT_SIZE + 2}
        fontWeight={LABEL_FONT_WEIGHT}
        opacity={textOpacity * LABEL_GLOW_OPACITY * 6}
        filter="url(#label-blur)"
      >
        We are here.
      </text>

      {/* Main text */}
      <text
        x={labelX}
        y={labelY + LABEL_FONT_SIZE / 3}
        textAnchor="start"
        fill={LABEL_TEXT_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={LABEL_FONT_SIZE}
        fontWeight={LABEL_FONT_WEIGHT}
        opacity={textOpacity}
      >
        We are here.
      </text>

      {/* Filter for glow */}
      <defs>
        <filter id="label-blur" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="6" />
        </filter>
      </defs>
    </svg>
  );
};

export default WeAreHereLabel;
