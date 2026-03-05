import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
} from "remotion";

export const Part5CompoundStatCalloutCisq: React.FC = () => {
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

  // Counter animation: rolls from $0 to $1.52T over 1.5s
  const counterDuration = 1.5 * fps;
  const counterProgress = interpolate(
    frame,
    [fadeInDuration * 0.5, fadeInDuration * 0.5 + counterDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );
  const counterValue = counterProgress * 1.52;
  const formattedCounter = `$${counterValue.toFixed(2)}T`;

  // Cascade delays for elements below the primary stat
  const cascadeDelay = 0.4 * fps;
  const statAnimDuration = 0.5 * fps;

  const animateElement = (index: number) => {
    const start = fadeInDuration + index * cascadeDelay;
    const opacity = interpolate(
      frame,
      [start, start + statAnimDuration],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    const translateY = interpolate(
      frame,
      [start, start + statAnimDuration],
      [24, 0],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      }
    );
    return { opacity, translateY };
  };

  const label = animateElement(0);
  const secondaryStat = animateElement(1);
  const secondaryLabel = animateElement(2);
  const source = animateElement(3);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        justifyContent: "center",
        alignItems: "flex-end",
        padding: 80,
      }}
    >
      <div
        style={{
          opacity: containerOpacity,
          width: 700,
          background: "rgba(30, 41, 59, 0.8)",
          backdropFilter: "blur(16px)",
          WebkitBackdropFilter: "blur(16px)",
          borderRadius: 20,
          border: "1px solid #334155",
          padding: "48px 52px",
          display: "flex",
          flexDirection: "column",
          gap: 16,
        }}
      >
        {/* Primary stat — counter animation */}
        <div
          style={{
            fontFamily: "Inter",
            fontWeight: 900,
            fontSize: 72,
            color: "#F59E0B",
            lineHeight: 1.1,
          }}
        >
          {formattedCounter}
        </div>

        {/* Label */}
        <div
          style={{
            opacity: label.opacity,
            transform: `translateY(${label.translateY}px)`,
            fontFamily: "Inter",
            fontWeight: 400,
            fontSize: 24,
            color: "rgba(255, 255, 255, 0.8)",
            lineHeight: 1.4,
          }}
        >
          annual US technical debt
        </div>

        {/* Divider */}
        <div
          style={{
            opacity: secondaryStat.opacity,
            width: "100%",
            height: 1,
            background: "rgba(255, 255, 255, 0.1)",
            marginTop: 8,
            marginBottom: 8,
          }}
        />

        {/* Secondary stat — compound formula */}
        <div
          style={{
            opacity: secondaryStat.opacity,
            transform: `translateY(${secondaryStat.translateY}px)`,
            fontFamily: "Inter",
            fontWeight: 700,
            fontSize: 36,
            color: "#EF4444",
            lineHeight: 1.2,
          }}
        >
          Debt × (1 + Rate)^Time
        </div>

        {/* Secondary label */}
        <div
          style={{
            opacity: secondaryLabel.opacity,
            transform: `translateY(${secondaryLabel.translateY}px)`,
            fontFamily: "Inter",
            fontWeight: 400,
            fontSize: 20,
            color: "rgba(239, 68, 68, 0.6)",
            lineHeight: 1.4,
          }}
        >
          compound interest curve
        </div>

        {/* Source */}
        <div
          style={{
            opacity: source.opacity,
            transform: `translateY(${source.translateY}px)`,
            fontFamily: "Inter",
            fontWeight: 300,
            fontSize: 16,
            color: "rgba(255, 255, 255, 0.6)",
            marginTop: 12,
            lineHeight: 1.4,
          }}
        >
          CISQ — The Cost of Poor Software Quality
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part5CompoundStatCalloutCisq;
