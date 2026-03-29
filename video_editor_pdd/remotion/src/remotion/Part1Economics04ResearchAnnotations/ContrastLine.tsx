import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CONTRAST_LINE_COLOR,
  CONTRAST_LINE_OPACITY,
  CONTRAST_LINE_START,
  CONTRAST_LINE_DRAW,
  GITHUB_CALLOUT_X,
  GITHUB_CALLOUT_Y,
  UPLEVEL_CALLOUT_X,
  UPLEVEL_CALLOUT_Y,
} from "./constants";

/** Dashed vertical line connecting the two annotation callout boxes. */
const ContrastLine: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame - CONTRAST_LINE_START;

  if (localFrame < 0) return null;

  const drawProgress = interpolate(
    localFrame,
    [0, CONTRAST_LINE_DRAW],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );

  // Line runs vertically between the two callout box positions
  // From bottom of Uplevel callout to top of GitHub callout
  const lineX = GITHUB_CALLOUT_X + 160; // center of 320px-wide callout
  const fromY = UPLEVEL_CALLOUT_Y + 90; // bottom of upper box
  const toY = GITHUB_CALLOUT_Y; // top of lower box
  const currentToY = fromY + (toY - fromY) * drawProgress;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <line
        x1={lineX}
        y1={fromY}
        x2={lineX}
        y2={currentToY}
        stroke={CONTRAST_LINE_COLOR}
        strokeWidth={1}
        strokeDasharray="4 4"
        opacity={CONTRAST_LINE_OPACITY * drawProgress}
      />
    </svg>
  );
};

export default ContrastLine;
