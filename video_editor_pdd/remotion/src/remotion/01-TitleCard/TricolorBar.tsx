import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

const SEGMENTS = [
  { color: "#22C55E", startFrame: 40, width: 133 },
  { color: "#F59E0B", startFrame: 45, width: 134 },
  { color: "#A855F7", startFrame: 50, width: 133 },
];

const BAR_Y = 520;
const BAR_HEIGHT = 3;
const FADE_OUT_START = 120;
const FADE_OUT_END = 150;

export const TricolorBar: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: BAR_Y,
        left: "50%",
        transform: "translateX(-50%)",
        display: "flex",
        height: BAR_HEIGHT,
        opacity: fadeOut,
      }}
    >
      {SEGMENTS.map((seg) => {
        const segWidth = interpolate(
          frame,
          [seg.startFrame, seg.startFrame + 20],
          [0, seg.width],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.inOut(Easing.cubic),
          }
        );

        return (
          <div
            key={seg.color}
            style={{
              width: segWidth,
              height: BAR_HEIGHT,
              backgroundColor: seg.color,
            }}
          />
        );
      })}
    </div>
  );
};

export default TricolorBar;
