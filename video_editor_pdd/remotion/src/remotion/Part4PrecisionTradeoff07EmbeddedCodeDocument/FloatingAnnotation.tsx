import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  FONT_SANS,
  ANNOTATION_TEXT_COLOR,
  LABEL_NL_COLOR,
  LABEL_CODE_COLOR,
  ANNOTATION_START,
} from "./constants";

export const FloatingAnnotation: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANNOTATION_START, ANNOTATION_START + 20],
    [0, 0.6],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [ANNOTATION_START, ANNOTATION_START + 20],
    [8, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (frame < ANNOTATION_START) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 920,
        width: 1920,
        display: "flex",
        justifyContent: "center",
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      <span
        style={{
          fontFamily: FONT_SANS,
          fontSize: 14,
          color: ANNOTATION_TEXT_COLOR,
        }}
      >
        Stay in{" "}
        <span style={{ color: LABEL_NL_COLOR }}>prompt space</span> as long as
        possible. Dip into{" "}
        <span style={{ color: LABEL_CODE_COLOR }}>code</span> when you must.
      </span>
    </div>
  );
};
