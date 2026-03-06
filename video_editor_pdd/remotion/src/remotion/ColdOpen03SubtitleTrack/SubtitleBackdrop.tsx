import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

const BACKDROP_FILL = "rgba(15, 23, 42, 0.75)";
const BACKDROP_BLUR = 8;
const BACKDROP_BORDER_COLOR = "rgba(59, 130, 246, 0.15)";
const BACKDROP_HEIGHT = 176;
const FADE_IN_FRAMES = 12;

export const SubtitleBackdrop: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, FADE_IN_FRAMES], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  return (
    <div
      style={{
        position: "absolute",
        bottom: 0,
        left: 0,
        width: "100%",
        height: BACKDROP_HEIGHT,
        backgroundColor: BACKDROP_FILL,
        backdropFilter: `blur(${BACKDROP_BLUR}px)`,
        WebkitBackdropFilter: `blur(${BACKDROP_BLUR}px)`,
        borderTop: `1px solid ${BACKDROP_BORDER_COLOR}`,
        opacity,
      }}
    />
  );
};

export default SubtitleBackdrop;
