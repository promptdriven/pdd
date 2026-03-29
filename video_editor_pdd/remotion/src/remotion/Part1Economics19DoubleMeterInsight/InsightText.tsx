import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TEXT_LIGHT,
  ACCENT_AND,
  CANVAS_W,
  INSIGHT_TEXT_START,
  INSIGHT_TEXT_END,
} from "./constants";

export const InsightText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [INSIGHT_TEXT_START, INSIGHT_TEXT_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [INSIGHT_TEXT_START, INSIGHT_TEXT_END],
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
        top: 900,
        left: 0,
        width: CANVAS_W,
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 28,
          fontWeight: 700,
          color: TEXT_LIGHT,
        }}
      >
        Bigger window{" "}
      </span>
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 28,
          fontWeight: 700,
          color: ACCENT_AND,
        }}
      >
        AND
      </span>
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 28,
          fontWeight: 700,
          color: TEXT_LIGHT,
        }}
      >
        {" "}smarter model.
      </span>
    </div>
  );
};
