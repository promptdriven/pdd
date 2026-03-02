import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";

export const Animation01BlueCircle: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateRight: "clamp",
  });

  const scale = interpolate(frame, [0, 30, 60], [1.0, 1.15, 1.0], {
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.ease),
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
          width: 240,
          height: 240,
          borderRadius: "50%",
          backgroundColor: "#3B82F6",
          boxShadow: "0 0 24px rgba(59, 130, 246, 0.5)",
          opacity,
          transform: `scale(${scale})`,
        }}
      />
    </AbsoluteFill>
  );
};

export default Animation01BlueCircle;
