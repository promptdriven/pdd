import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CONCLUSION_TEXT,
  CONCLUSION_Y,
  CONCLUSION_TEXT_COLOR,
  UNDERLINE_COLOR,
  CONCLUSION_START,
  CONCLUSION_FADE_END,
  UNDERLINE_DRAW_START,
  UNDERLINE_DRAW_END,
} from "./constants";

interface ConclusionTextProps {
  globalOpacity: number;
}

export const ConclusionText: React.FC<ConclusionTextProps> = ({
  globalOpacity,
}) => {
  const frame = useCurrentFrame();

  if (frame < CONCLUSION_START) return null;

  const textOpacity = interpolate(
    frame,
    [CONCLUSION_START, CONCLUSION_FADE_END],
    [0, 1],
    {
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const underlineProgress = interpolate(
    frame,
    [UNDERLINE_DRAW_START, UNDERLINE_DRAW_END],
    [0, 100],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: 960,
        top: CONCLUSION_Y,
        transform: "translateX(-50%)",
        opacity: textOpacity * globalOpacity,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
      }}
    >
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 600,
          fontSize: 24,
          color: CONCLUSION_TEXT_COLOR,
          whiteSpace: "nowrap",
        }}
      >
        {CONCLUSION_TEXT}
      </div>
      {/* Underline sweep */}
      <div
        style={{
          marginTop: 6,
          height: 2,
          width: `${underlineProgress}%`,
          backgroundColor: UNDERLINE_COLOR,
          alignSelf: "flex-start",
        }}
      />
    </div>
  );
};

export default ConclusionText;
