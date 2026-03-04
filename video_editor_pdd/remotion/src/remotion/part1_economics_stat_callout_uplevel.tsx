import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  useVideoConfig,
} from "remotion";

export const Part1EconomicsStatCalloutUplevel: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Card entrance: slides in from right and fades in over 0.5s
  const cardOpacity = interpolate(frame, [0, fps * 0.5], [0, 1], {
    extrapolateRight: "clamp",
  });
  const cardTranslateX = interpolate(frame, [0, fps * 0.5], [60, 0], {
    extrapolateRight: "clamp",
  });

  // Primary stat: fades in starting at frame 0, fully visible by 0.4s
  const primaryOpacity = interpolate(frame, [0, fps * 0.4], [0, 1], {
    extrapolateRight: "clamp",
  });
  const primaryTranslateY = interpolate(frame, [0, fps * 0.4], [20, 0], {
    extrapolateRight: "clamp",
  });

  // Secondary stat: enters 1s after primary
  const secondaryStart = fps * 1;
  const secondaryOpacity = interpolate(
    frame,
    [secondaryStart, secondaryStart + fps * 0.4],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const secondaryTranslateY = interpolate(
    frame,
    [secondaryStart, secondaryStart + fps * 0.4],
    [20, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Source line: fades in after secondary
  const sourceStart = fps * 1.6;
  const sourceOpacity = interpolate(
    frame,
    [sourceStart, sourceStart + fps * 0.4],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
      }}
    >
      {/* Card container */}
      <div
        style={{
          opacity: cardOpacity,
          transform: `translateX(${cardTranslateX}px)`,
          backgroundColor: "rgba(30, 41, 59, 0.8)",
          border: "1px solid #334155",
          borderRadius: 16,
          padding: "48px 56px",
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          gap: 24,
          width: 700,
          position: "absolute",
          right: 120,
        }}
      >
        {/* Primary stat */}
        <div
          style={{
            opacity: primaryOpacity,
            transform: `translateY(${primaryTranslateY}px)`,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
          }}
        >
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontWeight: 900,
              fontSize: 72,
              color: "#F59E0B",
              lineHeight: 1.1,
              textAlign: "center",
            }}
          >
            0%
          </span>
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontWeight: 900,
              fontSize: 36,
              color: "#F59E0B",
              lineHeight: 1.2,
              textAlign: "center",
              marginTop: 4,
            }}
          >
            throughput change
          </span>
        </div>

        {/* Divider */}
        <div
          style={{
            width: 120,
            height: 2,
            backgroundColor: "#334155",
            opacity: secondaryOpacity,
          }}
        />

        {/* Secondary stat */}
        <div
          style={{
            opacity: secondaryOpacity,
            transform: `translateY(${secondaryTranslateY}px)`,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
          }}
        >
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontWeight: 900,
              fontSize: 72,
              color: "#EF4444",
              lineHeight: 1.1,
              textAlign: "center",
            }}
          >
            41%
          </span>
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontWeight: 900,
              fontSize: 36,
              color: "#EF4444",
              lineHeight: 1.2,
              textAlign: "center",
              marginTop: 4,
            }}
          >
            more bugs
          </span>
        </div>

        {/* Source */}
        <span
          style={{
            opacity: sourceOpacity,
            fontFamily: "Inter, sans-serif",
            fontWeight: 300,
            fontSize: 16,
            color: "rgba(255, 255, 255, 0.6)",
            textAlign: "center",
            marginTop: 8,
          }}
        >
          Uplevel — 800 enterprise developers, 1 year
        </span>
      </div>
    </AbsoluteFill>
  );
};

export default Part1EconomicsStatCalloutUplevel;
