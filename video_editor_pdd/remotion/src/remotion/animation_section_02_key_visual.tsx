import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame } from "remotion";

const BARS = [0.35, 0.55, 0.8, 0.6];

export const AnimationSection02KeyVisual: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <AbsoluteFill style={{ backgroundColor: "#00FF00", justifyContent: "center", alignItems: "center", fontFamily: "sans-serif" }}>
      <div style={{ position: "absolute", top: 72, left: 72, color: "#F8FAFC", fontSize: 52, fontWeight: 700 }}>
        Key Visual
      </div>
      <div style={{ display: "flex", gap: 36, alignItems: "flex-end", height: 420 }}>
        {BARS.map((value, index) => {
          const scale = interpolate(frame, [0, 20 + index * 10, 90 + index * 10], [0, value, value], { extrapolateRight: "clamp" });
          return (
            <div
              key={index}
              style={{
                width: 120,
                height: 360 * scale,
                borderRadius: 24,
                background: index % 2 === 0 ? "#38BDF8" : "#22C55E",
                boxShadow: "0 12px 40px rgba(15, 23, 42, 0.45)",
              }}
            />
          );
        })}
      </div>
    </AbsoluteFill>
  );
};

export default AnimationSection02KeyVisual;
