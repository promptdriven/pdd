import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TITLE_COLOR,
  TITLE_OPACITY,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_FONT_FAMILY,
  TITLE_SLIDE_DISTANCE,
  GLOW_BLUR,
  GLOW_COLOR,
  GLOW_OPACITY_MIN,
  GLOW_OPACITY_MAX,
  GLOW_PULSE_START,
  GLOW_PULSE_CYCLE,
  CANVAS_WIDTH,
} from "./constants";

interface TitleLineProps {
  text: string;
  y: number;
  startFrame: number;
  animDuration: number;
}

/**
 * A single title line that fades in with a 10px upward slide.
 * After frame 100, the glow pulses gently between 0.08 and 0.12.
 */
export const TitleLine: React.FC<TitleLineProps> = ({
  text,
  y,
  startFrame,
  animDuration,
}) => {
  const frame = useCurrentFrame();

  const localFrame = frame - startFrame;
  if (localFrame < 0) return null;

  const opacity = interpolate(localFrame, [0, animDuration], [0, TITLE_OPACITY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const translateY = interpolate(
    localFrame,
    [0, animDuration],
    [TITLE_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Glow pulse after frame 100 (absolute)
  let glowOpacity = GLOW_OPACITY_MIN;
  if (frame >= GLOW_PULSE_START) {
    const pulseFrame = (frame - GLOW_PULSE_START) % GLOW_PULSE_CYCLE;
    glowOpacity = interpolate(
      pulseFrame,
      [0, GLOW_PULSE_CYCLE / 2, GLOW_PULSE_CYCLE],
      [GLOW_OPACITY_MIN, GLOW_OPACITY_MAX, GLOW_OPACITY_MIN],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.inOut(Easing.sin),
      }
    );
  }

  return (
    <div
      style={{
        position: "absolute",
        top: y,
        left: 0,
        width: CANVAS_WIDTH,
        display: "flex",
        justifyContent: "center",
        transform: `translateY(${translateY}px)`,
        opacity,
        pointerEvents: "none",
      }}
    >
      <span
        style={{
          fontFamily: TITLE_FONT_FAMILY,
          fontSize: TITLE_FONT_SIZE,
          fontWeight: TITLE_FONT_WEIGHT,
          color: TITLE_COLOR,
          textShadow: `0 0 ${GLOW_BLUR}px rgba(74, 144, 217, ${glowOpacity})`,
        }}
      >
        {text}
      </span>
    </div>
  );
};
