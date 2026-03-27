import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TEXT_PRIMARY_COLOR,
  ACCENT_AND_COLOR,
  FONT_FAMILY,
  CANVAS_WIDTH,
  INSIGHT_TEXT_Y,
  INSIGHT_TEXT_START,
  INSIGHT_TEXT_FADE_DURATION,
} from "./constants";

const InsightText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [INSIGHT_TEXT_START, INSIGHT_TEXT_START + INSIGHT_TEXT_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [INSIGHT_TEXT_START, INSIGHT_TEXT_START + INSIGHT_TEXT_FADE_DURATION],
    [16, 0],
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
        top: INSIGHT_TEXT_Y,
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
          color: TEXT_PRIMARY_COLOR,
        }}
      >
        Bigger window{" "}
      </span>
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 28,
          fontWeight: 700,
          color: ACCENT_AND_COLOR,
        }}
      >
        AND
      </span>
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 28,
          fontWeight: 700,
          color: TEXT_PRIMARY_COLOR,
        }}
      >
        {" "}smarter model.
      </span>
    </div>
  );
};

export default InsightText;
