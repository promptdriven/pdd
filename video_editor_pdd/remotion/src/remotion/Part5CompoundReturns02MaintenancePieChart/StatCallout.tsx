import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  FONT_FAMILY,
  STAT_FONT_SIZE,
  STAT_FONT_WEIGHT,
  STAT_TEXT_COLOR,
  STAT_OPACITY,
  STAT_FADE_DURATION,
} from "./constants";

interface StatCalloutProps {
  text: string;
  x: number;
  y: number;
  fadeStartFrame: number;
}

export const StatCallout: React.FC<StatCalloutProps> = ({
  text,
  x,
  y,
  fadeStartFrame,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [fadeStartFrame, fadeStartFrame + STAT_FADE_DURATION],
    [0, STAT_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (opacity <= 0) return null;

  return (
    <text
      x={x}
      y={y}
      fontFamily={FONT_FAMILY}
      fontSize={STAT_FONT_SIZE}
      fontWeight={STAT_FONT_WEIGHT}
      fill={STAT_TEXT_COLOR}
      opacity={opacity}
      textAnchor="middle"
      dominantBaseline="middle"
    >
      {text}
    </text>
  );
};
