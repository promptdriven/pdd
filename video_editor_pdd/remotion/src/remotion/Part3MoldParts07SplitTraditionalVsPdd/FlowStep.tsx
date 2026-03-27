import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  STEP_FILL,
  STEP_TEXT_COLOR,
  STEP_BORDER_OPACITY,
  STEP_BOX_RADIUS,
  STEP_HEIGHT,
  STEP_TEXT_SIZE,
  CODE_TEXT_SIZE,
  FADE_DURATION,
  PDD_GLOW_COLOR,
  GLOW_CYCLE,
} from "./constants";

interface FlowStepProps {
  text: string;
  stepWidth: number;
  borderColor: string;
  startFrame: number;
  hasBandaid: boolean;
  hasCode: boolean;
  codeText?: string;
  isFinal: boolean;
  centerX: number;
  y: number;
}

const BandAidIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg width={16} height={16} viewBox="0 0 16 16" style={{ marginLeft: 6, flexShrink: 0 }}>
    <rect x={2} y={5} width={12} height={6} rx={3} fill={color} opacity={0.4} />
    <rect x={5} y={2} width={6} height={12} rx={3} fill={color} opacity={0.4} />
    <circle cx={6.5} cy={7} r={0.8} fill={color} opacity={0.6} />
    <circle cx={9.5} cy={7} r={0.8} fill={color} opacity={0.6} />
    <circle cx={6.5} cy={9.5} r={0.8} fill={color} opacity={0.6} />
    <circle cx={9.5} cy={9.5} r={0.8} fill={color} opacity={0.6} />
  </svg>
);

export const FlowStep: React.FC<FlowStepProps> = ({
  text,
  stepWidth,
  borderColor,
  startFrame,
  hasBandaid,
  hasCode,
  codeText,
  isFinal,
  centerX,
  y,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [startFrame, startFrame + FADE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const translateY = interpolate(
    frame,
    [startFrame, startFrame + FADE_DURATION],
    [8, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Glow pulse for final PDD step
  const glowOpacity = isFinal && frame >= startFrame + FADE_DURATION
    ? interpolate(
        (frame - startFrame - FADE_DURATION) % GLOW_CYCLE,
        [0, GLOW_CYCLE / 2, GLOW_CYCLE],
        [0.1, 0.25, 0.1],
        { extrapolateRight: "clamp", easing: Easing.inOut(Easing.sin) }
      )
    : 0;

  return (
    <div
      style={{
        position: "absolute",
        left: centerX - stepWidth / 2,
        top: y,
        width: stepWidth,
        height: STEP_HEIGHT,
        opacity,
        transform: `translateY(${translateY}px)`,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        backgroundColor: STEP_FILL,
        borderRadius: STEP_BOX_RADIUS,
        border: `1px solid ${
          isFinal
            ? "rgba(74, 222, 128, 0.5)"
            : `${borderColor}${Math.round(STEP_BORDER_OPACITY * 255).toString(16).padStart(2, "0")}`
        }`,
        boxShadow: isFinal
          ? `0 0 8px rgba(74, 222, 128, ${glowOpacity})`
          : "none",
      }}
    >
      <div
        style={{
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          gap: 4,
        }}
      >
        {hasCode ? (
          <span style={{
            fontFamily: "Inter, sans-serif",
            fontSize: STEP_TEXT_SIZE,
            fontWeight: 400,
            color: STEP_TEXT_COLOR,
          }}>
            {text}{" "}
            <span style={{
              fontFamily: "JetBrains Mono, monospace",
              fontSize: CODE_TEXT_SIZE,
              color: PDD_GLOW_COLOR,
              opacity: 0.9,
            }}>
              ({codeText})
            </span>
          </span>
        ) : (
          <span style={{
            fontFamily: "Inter, sans-serif",
            fontSize: STEP_TEXT_SIZE,
            fontWeight: 400,
            color: isFinal ? PDD_GLOW_COLOR : STEP_TEXT_COLOR,
          }}>
            {text}
          </span>
        )}
        {hasBandaid && <BandAidIcon color={borderColor} />}
      </div>
    </div>
  );
};

export default FlowStep;
