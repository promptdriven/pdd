import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, spring } from "remotion";

interface CalloutBoxProps {
  appearFrame: number;
}

export const CalloutBox: React.FC<CalloutBoxProps> = ({ appearFrame }) => {
  const frame = useCurrentFrame();

  if (frame < appearFrame) return null;

  const localFrame = frame - appearFrame;

  // Slide up with spring
  const slideProgress = spring({
    frame: localFrame,
    fps: 30,
    config: { damping: 15, stiffness: 180 },
  });

  const translateY = interpolate(slideProgress, [0, 1], [40, 0]);
  const opacity = interpolate(localFrame, [0, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill>
      <div
        style={{
          position: "absolute",
          bottom: 40,
          left: 0,
          right: 0,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          transform: `translateY(${translateY}px)`,
          opacity,
        }}
      >
        {/* Callout container */}
        <div
          style={{
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            padding: "20px 48px",
            borderRadius: 12,
            backgroundColor: "rgba(239, 68, 68, 0.12)",
            border: "2px solid rgba(239, 68, 68, 0.4)",
          }}
        >
          {/* Main callout text */}
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontWeight: 700,
              fontSize: 32,
              color: "#EF4444",
              lineHeight: 1.3,
            }}
          >
            14-85% capability loss
          </span>

          {/* Source attribution */}
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontWeight: 400,
              fontSize: 16,
              color: "#94A3B8",
              marginTop: 6,
            }}
          >
            EMNLP 2024
          </span>
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default CalloutBox;
