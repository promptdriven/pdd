import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  INSIGHT_Y,
  FONT_FAMILY,
  COLOR_TEXT_PRIMARY,
  COLOR_ACCENT_AND,
  PHASE_TEXT_START,
  PHASE_TEXT_END,
} from "./constants";

export const InsightText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [PHASE_TEXT_START, PHASE_TEXT_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [PHASE_TEXT_START, PHASE_TEXT_END],
    [12, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: INSIGHT_Y,
        left: 0,
        width: CANVAS_WIDTH,
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 28,
          fontWeight: 700,
          color: COLOR_TEXT_PRIMARY,
        }}
      >
        Bigger window{" "}
      </span>
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 28,
          fontWeight: 700,
          color: COLOR_ACCENT_AND,
        }}
      >
        AND
      </span>
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 28,
          fontWeight: 700,
          color: COLOR_TEXT_PRIMARY,
        }}
      >
        {" "}smarter model.
      </span>
    </div>
  );
};

export default InsightText;
