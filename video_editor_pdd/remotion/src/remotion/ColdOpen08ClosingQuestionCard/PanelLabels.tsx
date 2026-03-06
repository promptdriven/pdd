import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  LEFT_LABEL,
  RIGHT_LABEL,
  LEFT_LABEL_COLOR,
  RIGHT_LABEL_COLOR,
  LABEL_FONT_SIZE,
  LABEL_PADDING_X,
  LABEL_BOTTOM_Y,
  CANVAS_WIDTH,
  LABEL_FADE_START,
  LABEL_FADE_END,
  FADE_OUT_START,
  FADE_OUT_END,
} from "./constants";

export const PanelLabels: React.FC = () => {
  const frame = useCurrentFrame();

  const leftLabelOpacity = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const rightLabelOpacity = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const fadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <>
      {/* Left label: "patching" */}
      <div
        style={{
          position: "absolute",
          left: LABEL_PADDING_X,
          top: LABEL_BOTTOM_Y,
          fontFamily: "'Inter', sans-serif",
          fontWeight: 400,
          fontSize: LABEL_FONT_SIZE,
          color: LEFT_LABEL_COLOR,
          opacity: leftLabelOpacity * fadeOut,
        }}
      >
        {LEFT_LABEL}
      </div>
      {/* Right label: "building" */}
      <div
        style={{
          position: "absolute",
          right: CANVAS_WIDTH - 1880,
          top: LABEL_BOTTOM_Y,
          fontFamily: "'Inter', sans-serif",
          fontWeight: 400,
          fontSize: LABEL_FONT_SIZE,
          color: RIGHT_LABEL_COLOR,
          opacity: rightLabelOpacity * fadeOut,
          textAlign: "right" as const,
        }}
      >
        {RIGHT_LABEL}
      </div>
    </>
  );
};

export default PanelLabels;
