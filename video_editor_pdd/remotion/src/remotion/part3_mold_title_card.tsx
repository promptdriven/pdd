import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
} from "remotion";

export const Part3MoldTitleCard: React.FC = () => {
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

  // Subtitle fade-in: staggered 10 frames after title (frames 10–40)
  const subtitleOpacity = interpolate(frame, [10, 40], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  const subtitleScale = interpolate(frame, [10, 40], [0.95, 1.0], {
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

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628" }}>
      {/* Background video */}
      <OffthreadVideo
        src={staticFile("veo/part3_mold.mp4")}
        style={{ width: "100%", height: "100%", objectFit: "cover" }}
      />

      {/* Dark overlay for text contrast */}
      <AbsoluteFill
        style={{
          backgroundColor: "rgba(0, 0, 0, 0.35)",
        }}
      />

      {/* Title + Subtitle container */}
      <AbsoluteFill
        style={{
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          justifyContent: "flex-start",
          paddingTop: "40%",
          opacity: fadeOut,
        }}
      >
        {/* Main title */}
        <div
          style={{
            opacity: titleOpacity,
            transform: `scale(${titleScale})`,
            fontFamily: "'Inter', sans-serif",
            fontWeight: 700,
            fontSize: 72,
            color: "#FFFFFF",
            textShadow: "0 2px 12px rgba(0,0,0,0.6)",
            letterSpacing: "-0.02em",
            textAlign: "center",
            width: "100%",
          }}
        >
          The Mold Has Three Parts
        </div>

        {/* Subtitle */}
        <div
          style={{
            opacity: subtitleOpacity,
            transform: `scale(${subtitleScale})`,
            fontFamily: "'Inter', sans-serif",
            fontWeight: 400,
            fontSize: 28,
            color: "rgba(255, 255, 255, 0.7)",
            marginTop: 12,
            textAlign: "center",
            width: "100%",
          }}
        >
          Test Capital · Prompt Capital · Grounding Capital
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part3MoldTitleCard;
