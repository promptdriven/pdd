import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  useVideoConfig,
} from "remotion";

export const Part3MoldStatCalloutDora: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const totalDuration = 5 * fps;
  const fadeInDuration = 0.5 * fps;
  const fadeOutStart = totalDuration - 0.5 * fps;

  // Overall opacity: fade in 0.5s, hold, fade out 0.5s
  const opacity = interpolate(
    frame,
    [0, fadeInDuration, fadeOutStart, totalDuration],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Left side enters first (starts at frame 0)
  const leftOpacity = interpolate(
    frame,
    [0, fadeInDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const leftSlide = interpolate(
    frame,
    [0, fadeInDuration],
    [-30, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Right side enters 1s later
  const rightDelay = 1 * fps;
  const rightOpacity = interpolate(
    frame,
    [rightDelay, rightDelay + fadeInDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const rightSlide = interpolate(
    frame,
    [rightDelay, rightDelay + fadeInDuration],
    [30, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Emphasis glow on right side after it appears
  const glowIntensity = interpolate(
    frame,
    [rightDelay + fadeInDuration, rightDelay + fadeInDuration + 0.5 * fps, rightDelay + fadeInDuration + 1.5 * fps],
    [0, 1, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Divider appears with right side
  const dividerOpacity = interpolate(
    frame,
    [rightDelay, rightDelay + fadeInDuration],
    [0, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Source text fades in after both sides visible
  const sourceDelay = rightDelay + fadeInDuration;
  const sourceOpacity = interpolate(
    frame,
    [sourceDelay, sourceDelay + 0.5 * fps],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        fontFamily: "Inter, sans-serif",
      }}
    >
      <div
        style={{
          opacity,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          position: "absolute",
          right: 120,
          top: "50%",
          transform: "translateY(-50%)",
        }}
      >
        {/* Card container */}
        <div
          style={{
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            backgroundColor: "rgba(30, 41, 59, 0.8)",
            border: "1px solid #334155",
            borderRadius: 16,
            padding: "48px 56px 36px",
            backdropFilter: "blur(12px)",
            position: "relative",
          }}
        >
          {/* Stats row */}
          <div
            style={{
              display: "flex",
              flexDirection: "row",
              alignItems: "center",
              gap: 0,
            }}
          >
            {/* Left stat */}
            <div
              style={{
                opacity: leftOpacity,
                transform: `translateX(${leftSlide}px)`,
                display: "flex",
                flexDirection: "column",
                alignItems: "center",
                width: 280,
                padding: "0 24px",
              }}
            >
              <div
                style={{
                  fontSize: 36,
                  fontWeight: 700,
                  color: "#EF4444",
                  lineHeight: 1.2,
                  textAlign: "center",
                  whiteSpace: "nowrap",
                }}
              >
                AI without tests
              </div>
              <div
                style={{
                  fontSize: 24,
                  fontWeight: 400,
                  color: "rgba(239, 68, 68, 0.8)",
                  marginTop: 12,
                  textAlign: "center",
                }}
              >
                = instability
              </div>
            </div>

            {/* Divider */}
            <div
              style={{
                width: 1,
                height: 100,
                backgroundColor: `rgba(255, 255, 255, ${dividerOpacity})`,
                flexShrink: 0,
              }}
            />

            {/* Right stat */}
            <div
              style={{
                opacity: rightOpacity,
                transform: `translateX(${rightSlide}px)`,
                display: "flex",
                flexDirection: "column",
                alignItems: "center",
                width: 320,
                padding: "0 24px",
                position: "relative",
              }}
            >
              {/* Emphasis glow */}
              <div
                style={{
                  position: "absolute",
                  top: -20,
                  left: -10,
                  right: -10,
                  bottom: -20,
                  borderRadius: 12,
                  background: `radial-gradient(ellipse at center, rgba(34, 197, 94, ${glowIntensity * 0.15}) 0%, transparent 70%)`,
                  pointerEvents: "none",
                }}
              />
              <div
                style={{
                  fontSize: 36,
                  fontWeight: 700,
                  color: "#22C55E",
                  lineHeight: 1.2,
                  textAlign: "center",
                  whiteSpace: "nowrap",
                  textShadow: glowIntensity > 0
                    ? `0 0 ${20 * glowIntensity}px rgba(34, 197, 94, ${glowIntensity * 0.5})`
                    : "none",
                }}
              >
                AI with tests
              </div>
              <div
                style={{
                  fontSize: 24,
                  fontWeight: 400,
                  color: "rgba(34, 197, 94, 0.8)",
                  marginTop: 12,
                  textAlign: "center",
                }}
              >
                = delivery amplification
              </div>
            </div>
          </div>

          {/* Source */}
          <div
            style={{
              fontSize: 16,
              fontWeight: 300,
              color: `rgba(255, 255, 255, ${sourceOpacity})`,
              marginTop: 32,
              textAlign: "center",
            }}
          >
            DORA State of DevOps Report
          </div>
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part3MoldStatCalloutDora;
