import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

const TITLE = "Why You're Still Darning Socks";
const FADE_IN_END = 30;
const FADE_OUT_START = 90;
const FADE_OUT_END = 120;
const SCALE_START = 0.92;
const SCALE_END = 1.0;

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeInOpacity = interpolate(frame, [0, FADE_IN_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const fadeOutOpacity = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  const opacity = fadeInOpacity * fadeOutOpacity;

  const scale = interpolate(frame, [0, FADE_IN_END], [SCALE_START, SCALE_END], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  return (
    <div
      style={{
        position: "absolute",
        top: "37%",
        left: "50%",
        transform: `translate(-50%, -50%) scale(${scale})`,
        opacity,
        fontFamily: "'Inter', sans-serif",
        fontWeight: 700,
        fontSize: 72,
        color: "#FFFFFF",
        textShadow: "0 4px 16px rgba(0, 0, 0, 0.6)",
        letterSpacing: "-0.02em",
        lineHeight: 1.1,
        textAlign: "center" as const,
        width: 1400,
      }}
    >
      {TITLE}
    </div>
  );
};

export default TitleText;
