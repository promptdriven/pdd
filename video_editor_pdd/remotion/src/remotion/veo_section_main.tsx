import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile, useCurrentFrame, useVideoConfig } from "remotion";

export const VeoSectionMain: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const sec = frame / fps;

  return (
    <AbsoluteFill style={{ backgroundColor: "#000" }}>
      <OffthreadVideo
        src={staticFile("veo/veo_section.mp4")}
        style={{ width: "100%", height: "100%", objectFit: "cover" }}
      />
      <div style={{
        position: "absolute", bottom: 80, left: 0, right: 0,
        textAlign: "center", color: "#fff", fontSize: 32,
        textShadow: "0 2px 8px rgba(0,0,0,0.8)",
        fontFamily: "sans-serif",
      }}>
        {sec.toFixed(1)}s
      </div>
    </AbsoluteFill>
  );
};

export default VeoSectionMain;
