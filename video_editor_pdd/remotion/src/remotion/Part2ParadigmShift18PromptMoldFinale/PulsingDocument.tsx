import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PROMPT_COLOR,
  PROMPT_X,
  PROMPT_Y,
  PROMPT_WIDTH,
  PROMPT_HEIGHT,
  PROMPT_FADE_DURATION,
  PULSE_CYCLE,
} from "./constants";

export const PulsingDocument: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in over first 30 frames
  const opacity = interpolate(frame, [0, PROMPT_FADE_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Pulsing glow on 45-frame sine cycle
  const pulsePhase = (frame % PULSE_CYCLE) / PULSE_CYCLE;
  const pulseT = Math.sin(pulsePhase * Math.PI * 2) * 0.5 + 0.5;
  const glowOpacity = interpolate(pulseT, [0, 1], [0.1, 0.35]);
  const glowBlur = interpolate(pulseT, [0, 1], [20, 40]);

  return (
    <div
      style={{
        position: "absolute",
        left: PROMPT_X,
        top: PROMPT_Y,
        width: PROMPT_WIDTH,
        height: PROMPT_HEIGHT,
        opacity,
      }}
    >
      {/* Glow layer */}
      <div
        style={{
          position: "absolute",
          inset: -15,
          borderRadius: 20,
          background: PROMPT_COLOR,
          opacity: glowOpacity,
          filter: `blur(${glowBlur}px)`,
        }}
      />
      {/* Document body */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          borderRadius: 12,
          border: `2px solid ${PROMPT_COLOR}`,
          backgroundColor: `${PROMPT_COLOR}19`,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 16,
            fontWeight: 700,
            color: PROMPT_COLOR,
            letterSpacing: 2,
          }}
        >
          PROMPT
        </span>
      </div>
    </div>
  );
};
