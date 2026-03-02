import React from "react";
import { AbsoluteFill, useCurrentFrame, useVideoConfig, interpolate } from "remotion";

export const AnimationSectionMain: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const progress = frame / (fps * 3);

  const circleScale = interpolate(progress, [0, 0.3, 0.5], [0, 1, 1], { extrapolateRight: "clamp" });
  const circleColor = progress < 0.5 ? "#3B82F6" : "#22C55E";
  const shapeRadius = progress >= 0.5 ? interpolate(progress, [0.5, 0.7], [50, 0], { extrapolateRight: "clamp" }) : 50;
  const slideX = progress >= 0.5 ? interpolate(progress, [0.5, 0.8], [0, 200], { extrapolateRight: "clamp" }) : 0;

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628", justifyContent: "center", alignItems: "center" }}>
      <div style={{
        width: 180, height: 180,
        backgroundColor: circleColor,
        borderRadius: shapeRadius + "%",
        transform: `scale(${circleScale}) translateX(${slideX}px)`,
      }} />
      <div style={{
        position: "absolute", bottom: 100, color: "#E2E8F0",
        fontSize: 36, fontFamily: "sans-serif", fontWeight: "bold",
        textAlign: "center",
      }}>
        animation section
      </div>
    </AbsoluteFill>
  );
};

export default AnimationSectionMain;
