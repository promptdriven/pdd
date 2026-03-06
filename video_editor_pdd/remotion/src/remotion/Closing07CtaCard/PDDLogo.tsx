import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  LOGO_FADE_START,
  LOGO_FADE_END,
  BRAND_BLUE,
  LOGO_SIZE,
  FINAL_FADE_START,
  FINAL_FADE_END,
} from "./constants";

export const PDDLogo: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [LOGO_FADE_START, LOGO_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const scale = interpolate(
    frame,
    [LOGO_FADE_START, LOGO_FADE_END],
    [0.85, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.4)),
    }
  );

  const fadeOut = interpolate(
    frame,
    [FINAL_FADE_START, FINAL_FADE_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <div
      style={{
        opacity: opacity * fadeOut,
        transform: `scale(${scale})`,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        marginBottom: 24,
      }}
    >
      <svg
        width={LOGO_SIZE}
        height={LOGO_SIZE}
        viewBox="0 0 64 64"
        fill="none"
      >
        {/* Hexagonal PDD logo mark */}
        <path
          d="M32 4L56 18V46L32 60L8 46V18L32 4Z"
          stroke={BRAND_BLUE}
          strokeWidth={2.5}
          fill="rgba(59, 130, 246, 0.1)"
        />
        <text
          x="32"
          y="38"
          textAnchor="middle"
          fontFamily="Inter, sans-serif"
          fontSize="18"
          fontWeight="800"
          fill={BRAND_BLUE}
          letterSpacing="0.05em"
        >
          PDD
        </text>
      </svg>
    </div>
  );
};
