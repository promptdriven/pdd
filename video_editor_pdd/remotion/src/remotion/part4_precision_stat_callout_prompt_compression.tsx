import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
} from "remotion";

export const Part4PrecisionStatCalloutPromptCompression: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const durationFrames = 5 * fps;
  const fadeInEnd = 0.5 * fps;
  const fadeOutStart = durationFrames - 0.5 * fps;

  // Overall opacity: fade in 0.5s, hold, fade out 0.5s
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

  // Animated counter: "50" → "10" over the hold period (0.5s to 3s)
  const counterAnimStart = fadeInEnd;
  const counterAnimEnd = 3 * fps;
  const promptLines = Math.round(
    interpolate(frame, [counterAnimStart, counterAnimEnd], [50, 10], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    })
  );

  // Animated test count: 0 → 47 over the same period
  const testCount = Math.round(
    interpolate(frame, [counterAnimStart, counterAnimEnd], [0, 47], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    })
  );

  // Arrow shrink: scale from 1 → 0.6 as counter animates
  const arrowScale = interpolate(
    frame,
    [counterAnimStart, counterAnimEnd],
    [1, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const statScale = interpolate(frame, [0, fadeInEnd], [0.8, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Secondary stat fades in slightly after primary
  const secondaryDelay = 0.3 * fps;
  const secondaryOpacity = interpolate(
    frame,
    [secondaryDelay, fadeInEnd + secondaryDelay],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

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
          opacity,
          transform: `translateY(${slideY}px)`,
          backgroundColor: "rgba(30, 41, 59, 0.8)",
          backdropFilter: "blur(12px)",
          WebkitBackdropFilter: "blur(12px)",
          border: "1px solid #334155",
          borderRadius: 16,
          padding: "48px 64px",
          width: 680,
          display: "flex",
          flexDirection: "column",
          gap: 12,
        }}
      >
        {/* Primary stat: "50 → 10 lines" with animated counter */}
        <div
          style={{
            display: "flex",
            alignItems: "baseline",
            gap: 12,
            transform: `scale(${statScale})`,
            transformOrigin: "left center",
          }}
        >
          <span
            style={{
              fontFamily: "Inter",
              fontWeight: 900,
              fontSize: 72,
              color: "#F59E0B",
              lineHeight: 1,
              fontVariantNumeric: "tabular-nums",
              minWidth: 80,
              display: "inline-block",
            }}
          >
            {promptLines}
          </span>
          <span
            style={{
              fontFamily: "Inter",
              fontWeight: 900,
              fontSize: 48,
              color: "#F59E0B",
              lineHeight: 1,
              transform: `scale(${arrowScale})`,
              display: "inline-block",
            }}
          >
            →
          </span>
          <span
            style={{
              fontFamily: "Inter",
              fontWeight: 900,
              fontSize: 72,
              color: "#F59E0B",
              lineHeight: 1,
            }}
          >
            10
          </span>
          <span
            style={{
              fontFamily: "Inter",
              fontWeight: 900,
              fontSize: 40,
              color: "rgba(245, 158, 11, 0.7)",
              lineHeight: 1,
              marginLeft: 4,
            }}
          >
            lines
          </span>
        </div>

        {/* Primary label */}
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
          prompt size as tests accumulate
        </div>

        {/* Divider */}
        <div
          style={{
            width: "100%",
            height: 1,
            backgroundColor: "rgba(51, 65, 85, 0.6)",
            marginTop: 12,
            marginBottom: 8,
          }}
        />

        {/* Secondary stat: "47 tests" with animated counter */}
        <div
          style={{
            opacity: secondaryOpacity,
            display: "flex",
            alignItems: "baseline",
            gap: 12,
          }}
        >
          <span
            style={{
              fontFamily: "Inter",
              fontWeight: 900,
              fontSize: 48,
              color: "#22C55E",
              lineHeight: 1,
              fontVariantNumeric: "tabular-nums",
            }}
          >
            {testCount}
          </span>
          <span
            style={{
              fontFamily: "Inter",
              fontWeight: 900,
              fontSize: 32,
              color: "#22C55E",
              lineHeight: 1,
            }}
          >
            tests
          </span>
        </div>

        {/* Secondary label */}
        <div
          style={{
            opacity: secondaryOpacity,
            fontFamily: "Inter",
            fontWeight: 400,
            fontSize: 20,
            color: "rgba(34, 197, 94, 0.6)",
            lineHeight: 1.4,
          }}
        >
          absorb edge-case precision
        </div>

        {/* Source */}
        <div
          style={{
            fontFamily: "Inter",
            fontWeight: 300,
            fontSize: 16,
            color: "rgba(255, 255, 255, 0.6)",
            lineHeight: 1.4,
            marginTop: 12,
          }}
        >
          PDD precision tradeoff
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionStatCalloutPromptCompression;
