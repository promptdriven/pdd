import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame } from "remotion";

export const AnimationSection03SplitSummary: React.FC = () => {
  const frame = useCurrentFrame();
  const dividerX = interpolate(frame, [0, 90], [640, 720], { extrapolateRight: "clamp" });

  return (
    <AbsoluteFill style={{ backgroundColor: "#FF0000", fontFamily: "sans-serif", color: "#E2E8F0" }}>
      <div style={{ position: "absolute", inset: 0, display: "flex" }}>
        <div style={{ flex: 1, backgroundColor: "#FF0000", display: "flex", justifyContent: "center", alignItems: "center" }}>
          <div style={{ fontSize: 46, fontWeight: 700 }}>Before</div>
        </div>
        <div style={{ flex: 1, backgroundColor: "#FF0000", display: "flex", justifyContent: "center", alignItems: "center" }}>
          <div style={{ fontSize: 46, fontWeight: 700 }}>After</div>
        </div>
      </div>
      <div style={{ position: "absolute", top: 0, bottom: 0, left: dividerX, width: 6, backgroundColor: "#38BDF8" }} />
      <div style={{ position: "absolute", top: 64, left: 64, fontSize: 54, fontWeight: 700 }}>
        Split Summary
      </div>
    </AbsoluteFill>
  );
};

export default AnimationSection03SplitSummary;
