import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  RESULT_WIDTH,
  RESULT_HEIGHT,
  PILLAR_RADIUS,
  RESULT_FADE_START,
  RESULT_FADE_END,
  WHITE,
} from "./constants";

interface ResultBoxProps {
  x: number;
  y: number;
}

export const ResultBox: React.FC<ResultBoxProps> = ({ x, y }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [RESULT_FADE_START, RESULT_FADE_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(4)),
  });

  const glowIntensity = interpolate(
    frame,
    [RESULT_FADE_START, RESULT_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    }
  );

  if (frame < RESULT_FADE_START) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y - RESULT_HEIGHT / 2,
        width: RESULT_WIDTH,
        height: RESULT_HEIGHT,
        opacity,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        borderRadius: PILLAR_RADIUS,
        border: `2px solid ${WHITE}`,
        backgroundColor: "rgba(255, 255, 255, 0.08)",
        boxShadow: `0 0 ${20 * glowIntensity}px rgba(255, 255, 255, ${0.3 * glowIntensity}), 0 0 ${40 * glowIntensity}px rgba(255, 255, 255, ${0.15 * glowIntensity})`,
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 900,
          fontSize: 28,
          color: WHITE,
          lineHeight: 1,
          textAlign: "center",
        }}
      >
        Complete Specification
      </span>
    </div>
  );
};
