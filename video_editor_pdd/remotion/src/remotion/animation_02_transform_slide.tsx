import React from "react";
import {
  AbsoluteFill,
  interpolate,
  interpolateColors,
  useCurrentFrame,
  Easing,
  spring,
  useVideoConfig,
} from "remotion";

export const Animation02TransformSlide: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Morph phase: frames 0–45 (circle → rounded square)
  const morphProgress = spring({
    frame,
    fps,
    config: { damping: 15, stiffness: 80, mass: 0.8 },
    durationInFrames: 45,
  });

  const borderRadius = interpolate(morphProgress, [0, 1], [120, 12]);
  const size = interpolate(morphProgress, [0, 1], [240, 200]);
  const fillColor = interpolateColors(
    morphProgress,
    [0, 1],
    ["#3B82F6", "#22C55E"]
  );

  // Slide phase: frames 45–120 (center → right)
  const slideX = interpolate(frame, [45, 120], [0, 25], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.ease),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#FF0000",
        justifyContent: "center",
        alignItems: "center",
      }}
    >
      <div
        style={{
          width: size,
          height: size,
          borderRadius,
          backgroundColor: fillColor,
          transform: `translateX(${slideX}vw)`,
        }}
      />
    </AbsoluteFill>
  );
};

export default Animation02TransformSlide;
