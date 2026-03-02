import React from "react";
import {
  AbsoluteFill,
  interpolate,
  interpolateColors,
  useCurrentFrame,
  Easing,
} from "remotion";

export const Animation02TransformSlide: React.FC = () => {
  const frame = useCurrentFrame();

  // Morph: frames 0–45
  const borderRadius = interpolate(frame, [0, 45], [120, 12], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const size = interpolate(frame, [0, 45], [240, 200], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const fillColor = interpolateColors(frame, [0, 45], ["#3B82F6", "#22C55E"]);

  // Slide: frames 45–105, easeInOut
  const translateX = interpolate(frame, [45, 105], [0, 300], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.ease),
  });

  // Shadow intensity follows morph completion
  const shadowOpacity = interpolate(frame, [0, 45], [0, 0.5], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Exit fade: last 30 frames (assuming ~150 total = 5s at 30fps)
  const opacity = interpolate(frame, [120, 150], [1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
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
          transform: `translateX(${translateX}px)`,
          boxShadow: `0 0 24px rgba(34, 197, 94, ${shadowOpacity})`,
          opacity,
        }}
      />
    </AbsoluteFill>
  );
};

export default Animation02TransformSlide;
