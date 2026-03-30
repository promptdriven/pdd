import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

const DIVIDER_FADE_DURATION = 15;
const DIVIDER_COLOR = "#FFFFFF";
const DIVIDER_OPACITY = 0.6;
const DIVIDER_THICKNESS = 2;
const HEIGHT = 1080;

export const SplitDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, DIVIDER_FADE_DURATION], [0, DIVIDER_OPACITY], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Draw-in effect: line grows from center outward
  const drawProgress = interpolate(frame, [0, DIVIDER_FADE_DURATION], [0, 1], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const lineHeight = HEIGHT * drawProgress;
  const yOffset = (HEIGHT - lineHeight) / 2;

  return (
    <div
      style={{
        position: "absolute",
        left: "50%",
        top: 0,
        width: DIVIDER_THICKNESS,
        height: HEIGHT,
        transform: "translateX(-50%)",
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        zIndex: 10,
      }}
    >
      <div
        style={{
          position: "absolute",
          top: yOffset,
          width: DIVIDER_THICKNESS,
          height: lineHeight,
          backgroundColor: DIVIDER_COLOR,
          opacity,
          borderRadius: 1,
        }}
      />
    </div>
  );
};

export default SplitDivider;
