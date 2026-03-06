import React from "react";
import { FONT_FAMILY, MUTED } from "./constants";

interface DocIconProps {
  x: number;
  y: number;
  width: number;
  height: number;
  color: string;
  label: string;
  sublabel: string;
  scale: number;
  opacity: number;
  labelOpacity: number;
  showCodeLines?: boolean;
}

export const DocIcon: React.FC<DocIconProps> = ({
  x,
  y,
  width,
  height,
  color,
  label,
  sublabel,
  scale,
  opacity,
  labelOpacity,
  showCodeLines = false,
}) => {
  return (
    <>
      {/* Document icon */}
      <div
        style={{
          position: "absolute",
          left: x,
          top: y,
          width,
          height,
          backgroundColor: color,
          borderRadius: 12,
          opacity,
          transform: `scale(${scale})`,
          transformOrigin: "center center",
          display: "flex",
          flexDirection: "column",
          justifyContent: "center",
          alignItems: "center",
          padding: 12,
          boxShadow: `0 0 30px ${color}40`,
        }}
      >
        {/* Code line decorations */}
        {showCodeLines &&
          [0.3, 0.5, 0.7, 0.4, 0.6, 0.55, 0.35].map((w, i) => (
            <div
              key={i}
              style={{
                width: `${w * 100}%`,
                height: 4,
                backgroundColor: "rgba(255,255,255,0.35)",
                borderRadius: 2,
                marginBottom: i < 6 ? 6 : 0,
                alignSelf: i % 2 === 0 ? "flex-start" : "flex-end",
              }}
            />
          ))}
        {!showCodeLines && (
          <>
            <div
              style={{
                width: "60%",
                height: 3,
                backgroundColor: "rgba(255,255,255,0.4)",
                borderRadius: 2,
                marginBottom: 5,
              }}
            />
            <div
              style={{
                width: "45%",
                height: 3,
                backgroundColor: "rgba(255,255,255,0.3)",
                borderRadius: 2,
                marginBottom: 5,
              }}
            />
            <div
              style={{
                width: "55%",
                height: 3,
                backgroundColor: "rgba(255,255,255,0.35)",
                borderRadius: 2,
              }}
            />
          </>
        )}
      </div>

      {/* Labels below the icon */}
      <div
        style={{
          position: "absolute",
          left: x - 20,
          top: y + height + 14,
          width: width + 40,
          textAlign: "center",
          opacity: labelOpacity,
        }}
      >
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontWeight: 600,
            fontSize: 22,
            color,
            lineHeight: 1.3,
          }}
        >
          {label}
        </div>
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontWeight: 400,
            fontSize: 18,
            color: MUTED,
            lineHeight: 1.3,
          }}
        >
          {sublabel}
        </div>
      </div>
    </>
  );
};
