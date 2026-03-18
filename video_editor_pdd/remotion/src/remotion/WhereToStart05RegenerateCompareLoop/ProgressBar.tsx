import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { PROGRESS_KEYFRAMES, COLORS } from "./constants";

export const ProgressBar: React.FC = () => {
  const frame = useCurrentFrame();

  // Compute progress value from keyframes
  const frames = PROGRESS_KEYFRAMES.map((k) => k.frame);
  const values = PROGRESS_KEYFRAMES.map((k) => k.value);

  const progress = interpolate(frame, frames as unknown as number[], values as unknown as number[], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const barWidth = 1100;
  const fillWidth = barWidth * Math.max(0, Math.min(1, progress));

  // Shimmer effect when progress resets (around frame 155)
  const shimmerOpacity =
    frame >= 148 && frame <= 165
      ? interpolate(frame, [148, 155, 165], [0, 0.4, 0], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : 0;

  return (
    <div
      style={{
        position: "absolute",
        top: 620,
        left: (1920 - barWidth) / 2,
        width: barWidth,
        height: 6,
      }}
    >
      {/* Track */}
      <div
        style={{
          position: "absolute",
          width: barWidth,
          height: 6,
          backgroundColor: COLORS.trackBg,
          borderRadius: 3,
        }}
      />
      {/* Fill */}
      <div
        style={{
          position: "absolute",
          width: fillWidth,
          height: 6,
          borderRadius: 3,
          background: `linear-gradient(90deg, ${COLORS.blue}, ${COLORS.green})`,
        }}
      />
      {/* Shimmer overlay */}
      {shimmerOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            width: barWidth,
            height: 6,
            borderRadius: 3,
            background: `linear-gradient(90deg, transparent, rgba(255,255,255,${shimmerOpacity}), transparent)`,
          }}
        />
      )}
    </div>
  );
};
