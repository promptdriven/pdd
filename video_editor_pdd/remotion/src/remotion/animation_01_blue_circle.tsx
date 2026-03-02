import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";

export const Animation01BlueCircle: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateRight: "clamp",
  });

  const scale = interpolate(frame, [0, 15, 30], [0.8, 1.1, 1.0], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.ease),
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
          width: 240,
          height: 240,
          borderRadius: "50%",
          backgroundColor: "#3B82F6",
          opacity,
          transform: `scale(${scale})`,
        }}
      />
    </AbsoluteFill>
  );
};

export default Animation01BlueCircle;
