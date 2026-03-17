import React from "react";
import { OffthreadVideo, useCurrentFrame, Easing, interpolate } from "remotion";
import {
  HEADER_FONT_SIZE,
  HEADER_FONT_WEIGHT,
  HEADER_LETTER_SPACING,
  HEADER_OPACITY,
  HEADER_Y,
  HEADER_FADE_START,
  HEADER_FADE_DUR,
} from "./constants";

export const SplitPanel: React.FC<{
  x: number;
  width: number;
  headerText: string;
  headerColor: string;
  gradeColor: string;
  gradeOpacity: number;
  vignetteEdge: string;
  videoSrc: string | null;
  children?: React.ReactNode;
}> = ({
  x,
  width,
  headerText,
  headerColor,
  gradeColor,
  gradeOpacity,
  vignetteEdge,
  videoSrc,
  children,
}) => {
  const frame = useCurrentFrame();

  const headerOpacity = interpolate(
    frame,
    [HEADER_FADE_START, HEADER_FADE_START + HEADER_FADE_DUR],
    [0, HEADER_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: 0,
        width,
        height: 1080,
        overflow: "hidden",
      }}
    >
      {/* Video background */}
      {videoSrc && (
        <OffthreadVideo
          src={videoSrc}
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: "100%",
            height: "100%",
            objectFit: "cover",
          }}
          muted
        />
      )}

      {/* Fallback dark bg if no video */}
      {!videoSrc && (
        <div
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: "100%",
            height: "100%",
            background: `linear-gradient(135deg, ${gradeColor}22 0%, #0A1628 100%)`,
          }}
        />
      )}

      {/* Color grade overlay */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          backgroundColor: gradeColor,
          opacity: gradeOpacity,
        }}
      />

      {/* Vignette */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          background: `radial-gradient(ellipse at center, transparent 40%, ${vignetteEdge} 100%)`,
          opacity: 0.3,
        }}
      />

      {/* Panel header */}
      <div
        style={{
          position: "absolute",
          top: HEADER_Y,
          left: 0,
          width: "100%",
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: HEADER_FONT_SIZE,
          fontWeight: HEADER_FONT_WEIGHT,
          letterSpacing: HEADER_LETTER_SPACING,
          color: headerColor,
          opacity: headerOpacity,
          textTransform: "uppercase",
        }}
      >
        {headerText}
      </div>

      {/* Panel-specific children (captions, icons, etc.) */}
      {children}
    </div>
  );
};

export default SplitPanel;
