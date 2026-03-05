import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, useVideoConfig } from "remotion";

export const Part1EconomicsStatCalloutGithub: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const durationFrames = 4 * fps;
  const fadeInEnd = 0.5 * fps;
  const fadeOutStart = durationFrames - 0.5 * fps;

  const opacity = interpolate(
    frame,
    [0, fadeInEnd, fadeOutStart, durationFrames],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const slideY = interpolate(
    frame,
    [0, fadeInEnd],
    [20, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const statScale = interpolate(
    frame,
    [0, fadeInEnd * 0.6, fadeInEnd],
    [0.8, 1.05, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628" }}>
      <div
        style={{
          position: "absolute",
          top: 120,
          right: 100,
          width: 520,
          opacity,
          transform: `translateY(${slideY}px)`,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          padding: "48px 40px 40px",
          borderRadius: 20,
          backgroundColor: "rgba(30, 41, 59, 0.8)",
          border: "1px solid #334155",
          backdropFilter: "blur(16px)",
          WebkitBackdropFilter: "blur(16px)",
        }}
      >
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 900,
            fontSize: 96,
            color: "#FFFFFF",
            lineHeight: 1,
            marginBottom: 12,
            transform: `scale(${statScale})`,
          }}
        >
          55%
        </div>

        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 400,
            fontSize: 24,
            color: "rgba(255, 255, 255, 0.8)",
            lineHeight: 1.3,
            textAlign: "center",
            marginBottom: 20,
          }}
        >
          speedup on individual tasks
        </div>

        <div
          style={{
            width: 60,
            height: 2,
            backgroundColor: "rgba(59, 130, 246, 0.4)",
            borderRadius: 1,
            marginBottom: 20,
          }}
        />

        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 300,
            fontSize: 16,
            color: "rgba(59, 130, 246, 0.6)",
            textAlign: "center",
            marginBottom: 8,
          }}
        >
          GitHub / Microsoft Study
        </div>

        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 400,
            fontSize: 14,
            color: "rgba(255, 255, 255, 0.45)",
            textAlign: "center",
          }}
        >
          95 developers, greenfield HTTP server
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part1EconomicsStatCalloutGithub;
