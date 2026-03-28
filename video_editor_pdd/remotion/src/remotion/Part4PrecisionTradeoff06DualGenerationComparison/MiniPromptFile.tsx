import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

interface MiniPromptFileProps {
  x: number;
  y: number;
  width: number;
  height: number;
  borderColor: string;
  badge: string;
  lineCount: number;
  appearStart: number;
  fadeDuration: number;
}

const MiniPromptFile: React.FC<MiniPromptFileProps> = ({
  x,
  y,
  width,
  height,
  borderColor,
  badge,
  lineCount,
  appearStart,
  fadeDuration,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [appearStart, appearStart + fadeDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const scale = interpolate(
    frame,
    [appearStart, appearStart + fadeDuration],
    [0.85, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Generate faint text lines to represent prompt content
  const lines = Array.from({ length: lineCount }, (_, i) => {
    const lineWidth = 40 + ((i * 37) % 50); // pseudo-random widths
    return (
      <div
        key={i}
        style={{
          height: 2,
          width: `${lineWidth}%`,
          backgroundColor: borderColor,
          opacity: 0.2,
          marginBottom: 3,
          borderRadius: 1,
        }}
      />
    );
  });

  return (
    <div
      style={{
        position: "absolute",
        left: x - width / 2,
        top: y,
        width,
        height,
        opacity,
        transform: `scale(${scale})`,
        transformOrigin: "center top",
      }}
    >
      {/* File container */}
      <div
        style={{
          width: "100%",
          height: "100%",
          border: `2px solid ${borderColor}`,
          borderRadius: 6,
          backgroundColor: "rgba(10, 15, 26, 0.8)",
          padding: 10,
          overflow: "hidden",
          boxSizing: "border-box",
          borderOpacity: 0.4,
        }}
      >
        {lines}
      </div>

      {/* Badge */}
      <div
        style={{
          position: "absolute",
          top: -12,
          right: 10,
          backgroundColor: borderColor,
          color: "#0A0F1A",
          fontFamily: "Inter, sans-serif",
          fontSize: 11,
          fontWeight: 600,
          padding: "2px 8px",
          borderRadius: 4,
        }}
      >
        {badge}
      </div>
    </div>
  );
};

export default MiniPromptFile;
