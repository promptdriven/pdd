// WeAreHereLabel.tsx — "We are here." annotation label with connector and pulse
import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  LABEL_TEXT_COLOR,
  LABEL_GLOW_COLOR,
  CONNECTOR_COLOR,
  FONT_FAMILY,
  ANNOTATION_SIZE,
  LABEL_X,
  LABEL_Y,
  CROSSING_2_X,
  CROSSING_2_Y,
  PHASE_LABEL_START,
  PHASE_LABEL_FADE_DURATION,
  LABEL_PULSE_PERIOD,
} from "./constants";

export const WeAreHereLabel: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < PHASE_LABEL_START) return null;

  const localFrame = frame - PHASE_LABEL_START;

  // Fade in over PHASE_LABEL_FADE_DURATION frames
  const fadeIn = interpolate(
    localFrame,
    [0, PHASE_LABEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Pulsing opacity between 0.8 and 1.0 after fade-in completes
  const pulsePhase = Math.max(0, localFrame - PHASE_LABEL_FADE_DURATION);
  const pulseT =
    (Math.sin((pulsePhase / LABEL_PULSE_PERIOD) * Math.PI * 2 - Math.PI / 2) +
      1) /
    2;
  const pulseOpacity = 0.8 + 0.2 * pulseT;
  const finalOpacity = fadeIn * pulseOpacity;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      {/* Connector line from label to crossing point */}
      <line
        x1={LABEL_X}
        y1={LABEL_Y - 8}
        x2={CROSSING_2_X}
        y2={CROSSING_2_Y}
        stroke={CONNECTOR_COLOR}
        strokeWidth={1.5}
        opacity={fadeIn * 0.3}
      />
      {/* Small dot at crossing point */}
      <circle
        cx={CROSSING_2_X}
        cy={CROSSING_2_Y}
        r={5}
        fill={CONNECTOR_COLOR}
        opacity={fadeIn * 0.5}
      />

      {/* Glow behind text */}
      <rect
        x={LABEL_X - 16}
        y={LABEL_Y - 6}
        width={220}
        height={44}
        rx={6}
        fill={LABEL_GLOW_COLOR}
        opacity={finalOpacity * 0.1}
      />

      {/* Background pill for readability */}
      <rect
        x={LABEL_X - 16}
        y={LABEL_Y - 6}
        width={220}
        height={44}
        rx={6}
        fill="#0A0F1A"
        opacity={finalOpacity * 0.7}
      />

      {/* Label text */}
      <text
        x={LABEL_X}
        y={LABEL_Y + 24}
        fill={LABEL_TEXT_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={ANNOTATION_SIZE}
        fontWeight={700}
        opacity={finalOpacity}
      >
        We are here.
      </text>
    </svg>
  );
};
