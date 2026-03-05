import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
} from "remotion";

export const ColdOpenTitleCard: React.FC = () => {
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

  // Fade-out over last 20 frames
  const fadeOut = interpolate(
    frame,
    [durationInFrames - 20, durationInFrames],
    [1, 0],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );

  const combinedOpacity = titleOpacity * fadeOut;

  return (
    <AbsoluteFill
      style={{
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        paddingTop: "0%",
      }}
    >
      <div
        style={{
          position: "absolute",
          top: "40%",
          left: "50%",
          transform: `translate(-50%, -50%) scale(${titleScale})`,
          opacity: combinedOpacity,
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
        Why You're Still Darning Socks
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpenTitleCard;
