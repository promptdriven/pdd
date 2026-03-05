import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  spring,
} from "remotion";

const CAPITALS = [
  {
    color: "#22C55E",
    label: "Test Capital",
    description: "Locks behavior permanently",
  },
  {
    color: "#F59E0B",
    label: "Prompt Capital",
    description: "Specifies intent in natural language",
  },
  {
    color: "#A855F7",
    label: "Grounding Capital",
    description: "Carries style across generations",
  },
];

export const ClosingStatCalloutRoi: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const durationFrames = 5 * fps;
  const fadeInEnd = 0.5 * fps;
  const fadeOutStart = durationFrames - 0.5 * fps;

  const containerOpacity = interpolate(
    frame,
    [0, fadeInEnd, fadeOutStart, durationFrames],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const statScale = spring({
    frame,
    fps,
    config: { damping: 12, stiffness: 100, mass: 0.8 },
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
          opacity: containerOpacity,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          backgroundColor: "rgba(30, 41, 59, 0.8)",
          backdropFilter: "blur(16px)",
          border: "1px solid #334155",
          borderRadius: 24,
          padding: "48px 64px",
          width: 720,
        }}
      >
        {/* Primary stat */}
        <div
          style={{
            fontSize: 64,
            fontWeight: 900,
            color: "#FFFFFF",
            transform: `scale(${statScale})`,
            lineHeight: 1.1,
            marginBottom: 8,
          }}
        >
          3 Capitals
        </div>

        {/* Label */}
        <div
          style={{
            fontSize: 22,
            fontWeight: 400,
            color: "rgba(255, 255, 255, 0.7)",
            marginBottom: 40,
          }}
        >
          that compound with every regeneration
        </div>

        {/* Three columns */}
        <div
          style={{
            display: "flex",
            gap: 32,
            width: "100%",
            justifyContent: "center",
          }}
        >
          {CAPITALS.map((cap, i) => {
            const delay = 8 + i * 6;
            const itemProgress = spring({
              frame: Math.max(0, frame - delay),
              fps,
              config: { damping: 14, stiffness: 120, mass: 0.6 },
            });

            return (
              <div
                key={cap.label}
                style={{
                  display: "flex",
                  flexDirection: "column",
                  alignItems: "center",
                  gap: 8,
                  flex: 1,
                  opacity: itemProgress,
                  transform: `translateY(${interpolate(itemProgress, [0, 1], [20, 0])}px)`,
                }}
              >
                {/* Icon circle */}
                <div
                  style={{
                    width: 48,
                    height: 48,
                    borderRadius: 24,
                    backgroundColor: cap.color,
                    opacity: 0.2,
                    display: "flex",
                    alignItems: "center",
                    justifyContent: "center",
                    position: "relative",
                  }}
                >
                  <div
                    style={{
                      position: "absolute",
                      width: 20,
                      height: 20,
                      borderRadius: 10,
                      backgroundColor: cap.color,
                    }}
                  />
                </div>

                {/* Label */}
                <div
                  style={{
                    fontSize: 20,
                    fontWeight: 600,
                    color: cap.color,
                    textAlign: "center",
                  }}
                >
                  {cap.label}
                </div>

                {/* Description */}
                <div
                  style={{
                    fontSize: 16,
                    fontWeight: 400,
                    color: "rgba(255, 255, 255, 0.6)",
                    textAlign: "center",
                    lineHeight: 1.4,
                  }}
                >
                  {cap.description}
                </div>
              </div>
            );
          })}
        </div>

        {/* Source */}
        <div
          style={{
            marginTop: 36,
            fontSize: 14,
            fontWeight: 400,
            color: "rgba(255, 255, 255, 0.4)",
            letterSpacing: 1,
          }}
        >
          PDD — Prompt-Driven Development
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default ClosingStatCalloutRoi;
