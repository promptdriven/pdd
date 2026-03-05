import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
} from "remotion";

export const Part3MoldStatCalloutNlContext: React.FC = () => {
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

  const slideY = interpolate(frame, [0, fadeInEnd], [20, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const statScale = interpolate(frame, [0, fadeInEnd], [0.8, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        justifyContent: "flex-start",
        alignItems: "flex-start",
        padding: 80,
      }}
    >
      <div
        style={{
          opacity,
          transform: `translateY(${slideY}px)`,
          backgroundColor: "rgba(30, 41, 59, 0.8)",
          backdropFilter: "blur(12px)",
          WebkitBackdropFilter: "blur(12px)",
          border: "1px solid #334155",
          borderRadius: 16,
          padding: "48px 56px",
          width: 620,
          display: "flex",
          flexDirection: "column",
          gap: 12,
        }}
      >
        {/* Stat number */}
        <div
          style={{
            fontFamily: "Inter",
            fontWeight: 900,
            fontSize: 96,
            color: "#F59E0B",
            lineHeight: 1,
            transform: `scale(${statScale})`,
            transformOrigin: "left center",
          }}
        >
          41%
        </div>

        {/* Label */}
        <div
          style={{
            fontFamily: "Inter",
            fontWeight: 400,
            fontSize: 24,
            color: "rgba(255, 255, 255, 0.8)",
            lineHeight: 1.4,
            marginTop: 8,
          }}
        >
          code generation improvement from NL comments
        </div>

        {/* Source */}
        <div
          style={{
            fontFamily: "Inter",
            fontWeight: 300,
            fontSize: 16,
            color: "rgba(245, 158, 11, 0.6)",
            lineHeight: 1.4,
            marginTop: 8,
          }}
        >
          Natural language context study
        </div>

        {/* Subtext */}
        <div
          style={{
            fontFamily: "Inter",
            fontWeight: 300,
            fontSize: 18,
            color: "rgba(255, 255, 255, 0.5)",
            lineHeight: 1.4,
            marginTop: 4,
          }}
        >
          Models trained on 30x more NL than code
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part3MoldStatCalloutNlContext;
