import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  useVideoConfig,
  spring,
} from "remotion";

export const Part1EconomicsStatCalloutGitclear: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Card entrance: scale + fade in over first 15 frames
  const cardScale = spring({ frame, fps, config: { damping: 14, mass: 0.8 } });
  const cardOpacity = interpolate(frame, [0, 10], [0, 1], {
    extrapolateRight: "clamp",
  });

  // Counter animation for "44%" — counts up from 0 to 44 over frames 5–45
  const churnValue = Math.round(
    interpolate(frame, [5, 45], [0, 44], { extrapolateLeft: "clamp", extrapolateRight: "clamp" })
  );

  // Counter animation for "60%" — counts down from 0 to 60 over frames 15–55
  const refactorValue = Math.round(
    interpolate(frame, [15, 55], [0, 60], { extrapolateLeft: "clamp", extrapolateRight: "clamp" })
  );

  // Stagger the two stats
  const stat1Opacity = interpolate(frame, [3, 12], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const stat1Y = interpolate(frame, [3, 12], [20, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const stat2Opacity = interpolate(frame, [13, 22], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const stat2Y = interpolate(frame, [13, 22], [20, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Source line fades in after stats
  const sourceOpacity = interpolate(frame, [50, 65], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Exit fade near the end (5s at 30fps = 150 frames)
  const exitOpacity = interpolate(frame, [130, 148], [1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        fontFamily: "Inter, sans-serif",
      }}
    >
      <div
        style={{
          opacity: cardOpacity * exitOpacity,
          transform: `scale(${cardScale})`,
          backgroundColor: "rgba(30, 41, 59, 0.8)",
          border: "1px solid #334155",
          borderRadius: 24,
          padding: "60px 80px",
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          gap: 40,
          width: 720,
        }}
      >
        {/* Primary stat: churn */}
        <div
          style={{
            opacity: stat1Opacity,
            transform: `translateY(${stat1Y}px)`,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            gap: 4,
          }}
        >
          <span
            style={{
              fontSize: 72,
              fontWeight: 900,
              color: "#EF4444",
              lineHeight: 1,
              letterSpacing: -2,
            }}
          >
            {churnValue}% more churn
          </span>
        </div>

        {/* Secondary stat: refactoring */}
        <div
          style={{
            opacity: stat2Opacity,
            transform: `translateY(${stat2Y}px)`,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            gap: 4,
          }}
        >
          <span
            style={{
              fontSize: 72,
              fontWeight: 900,
              color: "#F59E0B",
              lineHeight: 1,
              letterSpacing: -2,
            }}
          >
            {refactorValue}% less refactoring
          </span>
        </div>

        {/* Source */}
        <span
          style={{
            opacity: sourceOpacity,
            fontSize: 16,
            fontWeight: 300,
            color: "rgba(255, 255, 255, 0.6)",
            marginTop: 8,
          }}
        >
          GitClear — 211 million lines analyzed
        </span>
      </div>
    </AbsoluteFill>
  );
};

export default Part1EconomicsStatCalloutGitclear;
