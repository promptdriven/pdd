import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame } from "remotion";

export const VeoSection01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [0, 18, 120], [0, 1, 1], { extrapolateRight: "clamp" });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        justifyContent: "center",
        alignItems: "center",
        color: "#F8FAFC",
        fontFamily: "sans-serif",
      }}
    >
      <div style={{ opacity, textAlign: "center" }}>
        <div style={{ fontSize: 24, letterSpacing: 6, textTransform: "uppercase", color: "#38BDF8" }}>
          Deterministic Render
        </div>
        <div style={{ fontSize: 72, fontWeight: 700, marginTop: 24 }}>
          Title Card
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default VeoSection01TitleCard;
