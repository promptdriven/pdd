import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
} from "remotion";

export const ClosingTitleCard: React.FC = () => {
  const frame = useCurrentFrame();
  const { durationInFrames } = useVideoConfig();

  // Title fade-in: frames 0–30
  const titleOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  const titleScale = interpolate(frame, [0, 30], [0.95, 1.0], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Subtitle fades in 10 frames after title (staggered)
  const subtitleOpacity = interpolate(frame, [10, 40], [0, 0.7], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Fade-out over last 20 frames
  const fadeOut = interpolate(
    frame,
    [durationInFrames - 20, durationInFrames],
    [1, 0],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );

  const combinedTitleOpacity = titleOpacity * fadeOut;
  const combinedSubtitleOpacity = subtitleOpacity * fadeOut;

  return (
    <AbsoluteFill
      style={{
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
      }}
    >
      <div
        style={{
          position: "absolute",
          top: "40%",
          left: "50%",
          transform: `translate(-50%, -50%) scale(${titleScale})`,
          opacity: combinedTitleOpacity,
          fontFamily: "'Inter', sans-serif",
          fontWeight: 700,
          fontSize: 72,
          color: "#FFFFFF",
          textShadow: "0 2px 12px rgba(0,0,0,0.6)",
          letterSpacing: "-0.02em",
          textAlign: "center",
          width: 1400,
          lineHeight: 1.2,
        }}
      >
        Stop Darning
      </div>
      <div
        style={{
          position: "absolute",
          top: "calc(40% + 48px)",
          left: "50%",
          transform: "translate(-50%, 0)",
          opacity: combinedSubtitleOpacity,
          fontFamily: "'Inter', sans-serif",
          fontWeight: 400,
          fontSize: 28,
          color: "#FFFFFF",
          textShadow: "0 2px 12px rgba(0,0,0,0.6)",
          textAlign: "center",
          width: 1400,
        }}
      >
        Build the Mold
      </div>
    </AbsoluteFill>
  );
};

export default ClosingTitleCard;
