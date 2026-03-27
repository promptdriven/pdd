import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

interface SplitDividerProps {
  canvasWidth: number;
  canvasHeight: number;
  dividerColor: string;
  dividerWidthPx: number;
  dividerOpacity: number;
  fadeFrames: number;
}

export const SplitDivider: React.FC<SplitDividerProps> = ({
  canvasWidth,
  canvasHeight,
  dividerColor,
  dividerWidthPx,
  dividerOpacity,
  fadeFrames,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, fadeFrames], [0, dividerOpacity], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Divider draws from top to bottom over fadeFrames
  const drawProgress = interpolate(frame, [0, fadeFrames], [0, 1], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: "absolute",
        left: canvasWidth / 2 - dividerWidthPx / 2,
        top: 0,
        width: dividerWidthPx,
        height: canvasHeight * drawProgress,
        backgroundColor: dividerColor,
        opacity,
        zIndex: 10,
      }}
    />
  );
};

export default SplitDivider;
