import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile, useVideoConfig } from "remotion";

import { useVisualMediaSrc } from "./visual-runtime";

type GeneratedMediaVisualConfig = Record<string, string | boolean>;

const lowerThirdLayout = (width: number, height: number) => {
  const scaleX = width / 1920;
  const scaleY = height / 1080;

  return {
    leftPadding: Math.max(32, 80 * scaleX),
    barHeight: Math.max(48, 80 * scaleY),
    bottomOffset: Math.max(32, 120 * scaleY),
    fontSize: Math.max(16, 20 * Math.min(scaleX, scaleY)),
  };
};

export const GeneratedMediaVisual: React.FC<{
  config?: GeneratedMediaVisualConfig | null;
}> = ({ config }) => {
  const src = useVisualMediaSrc("defaultSrc");
  const { width, height } = useVideoConfig();
  const layout = lowerThirdLayout(width, height);
  const gradientOverlay = config?.gradientOverlay;
  const lowerThirdText =
    typeof config?.lowerThirdText === "string" ? config.lowerThirdText : null;
  const lightBloom = config?.lightBloom === true;

  return (
    <AbsoluteFill style={{ backgroundColor: "#000000" }}>
      {src ? (
        <OffthreadVideo
          src={staticFile(src)}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
        />
      ) : null}

      {gradientOverlay === "bottom" ? (
        <AbsoluteFill
          style={{
            background:
              "linear-gradient(180deg, rgba(10,22,40,0) 0%, rgba(10,22,40,0) 60%, rgba(10,22,40,0.6) 100%)",
            pointerEvents: "none",
          }}
        />
      ) : null}

      {lightBloom ? (
        <AbsoluteFill
          style={{
            background:
              "radial-gradient(circle at 82% 12%, rgba(255,220,150,0.18) 0%, rgba(255,220,150,0.08) 18%, rgba(255,220,150,0) 38%)",
            pointerEvents: "none",
          }}
        />
      ) : null}

      {lowerThirdText ? (
        <div
          style={{
            position: "absolute",
            left: 0,
            right: 0,
            bottom: layout.bottomOffset,
            height: layout.barHeight,
            backgroundColor: "rgba(0,0,0,0.5)",
            display: "flex",
            alignItems: "center",
            paddingLeft: layout.leftPadding,
            paddingRight: layout.leftPadding,
            color: "#FFFFFF",
            fontFamily: "'Inter', sans-serif",
            fontSize: layout.fontSize,
            fontWeight: 500,
            opacity: 0.9,
          }}
        >
          {lowerThirdText}
        </div>
      ) : null}
    </AbsoluteFill>
  );
};

export default GeneratedMediaVisual;
