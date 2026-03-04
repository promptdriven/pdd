import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
} from "remotion";

export const Part3MoldStatCalloutCoderabbit: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const totalDuration = 5 * fps;
  const fadeInDuration = 0.5 * fps;
  const fadeOutStart = totalDuration - 0.5 * fps;

  // Overall container opacity: fade in 0.5s, hold, fade out 0.5s
  const containerOpacity = interpolate(
    frame,
    [0, fadeInDuration, fadeOutStart, totalDuration],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Cascade delays: each stat appears 0.5s apart
  const cascadeDelay = 0.5 * fps;
  const statAnimDuration = 0.5 * fps;

  const animateStat = (index: number) => {
    const start = index * cascadeDelay;
    const opacity = interpolate(
      frame,
      [start, start + statAnimDuration],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    const translateY = interpolate(
      frame,
      [start, start + statAnimDuration],
      [30, 0],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      }
    );
    return { opacity, translateY };
  };

  const stat0 = animateStat(0);
  const stat1 = animateStat(1);
  const stat2 = animateStat(2);
  const stat3 = animateStat(3);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        justifyContent: "flex-start",
        alignItems: "flex-end",
        padding: 60,
      }}
    >
      <div
        style={{
          opacity: containerOpacity,
          width: 720,
          marginTop: 80,
          background: "rgba(30, 41, 59, 0.8)",
          backdropFilter: "blur(16px)",
          WebkitBackdropFilter: "blur(16px)",
          borderRadius: 20,
          border: "1px solid #334155",
          padding: "48px 52px",
          display: "flex",
          flexDirection: "column",
          gap: 28,
        }}
      >
        {/* Primary stat */}
        <div
          style={{
            opacity: stat0.opacity,
            transform: `translateY(${stat0.translateY}px)`,
            fontFamily: "Inter",
            fontWeight: 900,
            fontSize: 72,
            color: "#EF4444",
            lineHeight: 1.1,
          }}
        >
          1.7x more issues
        </div>

        {/* Secondary stat */}
        <div
          style={{
            opacity: stat1.opacity,
            transform: `translateY(${stat1.translateY}px)`,
            fontFamily: "Inter",
            fontWeight: 900,
            fontSize: 48,
            color: "#F59E0B",
            lineHeight: 1.2,
          }}
        >
          75% more logic errors
        </div>

        {/* Tertiary stat */}
        <div
          style={{
            opacity: stat2.opacity,
            transform: `translateY(${stat2.translateY}px)`,
            fontFamily: "Inter",
            fontWeight: 900,
            fontSize: 48,
            color: "#EF4444",
            lineHeight: 1.2,
          }}
        >
          8x performance problems
        </div>

        {/* Source */}
        <div
          style={{
            opacity: stat3.opacity,
            transform: `translateY(${stat3.translateY}px)`,
            fontFamily: "Inter",
            fontWeight: 300,
            fontSize: 16,
            color: "rgba(255, 255, 255, 0.6)",
            marginTop: 8,
            lineHeight: 1.4,
          }}
        >
          CodeRabbit — AI-generated code analysis
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part3MoldStatCalloutCoderabbit;
