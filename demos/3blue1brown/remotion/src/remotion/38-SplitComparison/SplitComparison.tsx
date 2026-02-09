import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, OffthreadVideo, staticFile } from "remotion";
import { COLORS, BEATS, SplitComparisonPropsType } from "./constants";

// Main SplitComparison Component
export const SplitComparison: React.FC<SplitComparisonPropsType> = ({
  showDivider = true,
  dividerOpacityMax = 0.5,
}) => {
  const frame = useCurrentFrame();

  // Divider opacity animation (0-1s fade in)
  const dividerOpacity = interpolate(
    frame,
    [BEATS.DIVIDER_FADE_START, BEATS.DIVIDER_FADE_END],
    [0, dividerOpacityMax],
    { extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill>
      {/* Video base layer */}
      <OffthreadVideo
        loop
        src={staticFile("split_3d_vs_mold.mp4")}
        style={{ width: "100%", height: "100%", objectFit: "cover" }}
      />

      {/* Center divider */}
      {showDivider && (
        <div
          style={{
            position: "absolute",
            left: "50%",
            top: 0,
            width: 2,
            height: "100%",
            backgroundColor: COLORS.DIVIDER_WHITE,
            opacity: dividerOpacity,
            transform: "translateX(-50%)",
          }}
        />
      )}
    </AbsoluteFill>
  );
};
