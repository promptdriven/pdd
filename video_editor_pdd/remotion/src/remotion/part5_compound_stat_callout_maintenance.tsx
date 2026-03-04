import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
} from "remotion";

export const Part5CompoundStatCalloutMaintenance: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const totalDuration = 6 * fps;
  const fadeInDuration = 0.5 * fps;
  const fadeOutStart = totalDuration - 0.5 * fps;

  // Overall container opacity: fade in 0.5s, hold 5s, fade out 0.5s
  const containerOpacity = interpolate(
    frame,
    [0, fadeInDuration, fadeOutStart, totalDuration],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Counter animation: rolls from 0% to 90% over 1.5s
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
  const counterValue = Math.round(counterProgress * 90);

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
  const secondary1 = animateElement(1);
  const secondary2 = animateElement(2);
  const source = animateElement(3);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        justifyContent: "center",
        alignItems: "center",
      }}
    >
      <div
        style={{
          opacity: containerOpacity,
          width: 760,
          background: "rgba(30, 41, 59, 0.8)",
          backdropFilter: "blur(16px)",
          WebkitBackdropFilter: "blur(16px)",
          borderRadius: 20,
          border: "1px solid #334155",
          padding: "48px 56px",
          display: "flex",
          flexDirection: "column",
          gap: 12,
        }}
      >
        {/* Primary stat — counter animation 80–90% */}
        <div
          style={{
            fontFamily: "Inter",
            fontWeight: 900,
            fontSize: 84,
            color: "#EF4444",
            lineHeight: 1.1,
          }}
        >
          80–{counterValue}%
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
          of software cost is maintenance
        </div>

        {/* Divider */}
        <div
          style={{
            opacity: secondary1.opacity,
            width: "100%",
            height: 1,
            background: "rgba(255, 255, 255, 0.1)",
            marginTop: 8,
            marginBottom: 8,
          }}
        />

        {/* Secondary stat row */}
        <div
          style={{
            display: "flex",
            gap: 32,
          }}
        >
          {/* McKinsey stat */}
          <div
            style={{
              opacity: secondary1.opacity,
              transform: `translateY(${secondary1.translateY}px)`,
              flex: 1,
              display: "flex",
              flexDirection: "column",
              gap: 4,
            }}
          >
            <div
              style={{
                fontFamily: "Inter",
                fontWeight: 700,
                fontSize: 40,
                color: "#F59E0B",
                lineHeight: 1.2,
              }}
            >
              +40%
            </div>
            <div
              style={{
                fontFamily: "Inter",
                fontWeight: 400,
                fontSize: 18,
                color: "rgba(255, 255, 255, 0.6)",
                lineHeight: 1.4,
              }}
            >
              maintenance spend with high tech debt
            </div>
            <div
              style={{
                fontFamily: "Inter",
                fontWeight: 300,
                fontSize: 14,
                color: "rgba(255, 255, 255, 0.5)",
                lineHeight: 1.4,
                marginTop: 2,
              }}
            >
              McKinsey
            </div>
          </div>

          {/* Stripe stat */}
          <div
            style={{
              opacity: secondary2.opacity,
              transform: `translateY(${secondary2.translateY}px)`,
              flex: 1,
              display: "flex",
              flexDirection: "column",
              gap: 4,
            }}
          >
            <div
              style={{
                fontFamily: "Inter",
                fontWeight: 700,
                fontSize: 40,
                color: "#F59E0B",
                lineHeight: 1.2,
              }}
            >
              33%
            </div>
            <div
              style={{
                fontFamily: "Inter",
                fontWeight: 400,
                fontSize: 18,
                color: "rgba(255, 255, 255, 0.6)",
                lineHeight: 1.4,
              }}
            >
              of dev time lost to debt
            </div>
            <div
              style={{
                fontFamily: "Inter",
                fontWeight: 300,
                fontSize: 14,
                color: "rgba(255, 255, 255, 0.5)",
                lineHeight: 1.4,
                marginTop: 2,
              }}
            >
              Stripe
            </div>
          </div>
        </div>

        {/* Source */}
        <div
          style={{
            opacity: source.opacity,
            transform: `translateY(${source.translateY}px)`,
            fontFamily: "Inter",
            fontWeight: 300,
            fontSize: 14,
            color: "rgba(255, 255, 255, 0.5)",
            marginTop: 12,
            lineHeight: 1.4,
          }}
        >
          McKinsey, Stripe developer surveys
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part5CompoundStatCalloutMaintenance;
