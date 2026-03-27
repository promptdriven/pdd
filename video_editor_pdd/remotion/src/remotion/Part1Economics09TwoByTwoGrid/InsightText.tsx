import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface InsightTextProps {
  text: string;
  color: string;
  fontSize: number;
  y: number;
  fadeStart: number;
  fadeDuration: number;
}

export const InsightText: React.FC<InsightTextProps> = ({
  text,
  color,
  fontSize,
  y,
  fadeStart,
  fadeDuration,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [fadeStart, fadeStart + fadeDuration],
    [0, 0.88],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [fadeStart, fadeStart + fadeDuration],
    [12, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: y,
        width: 1920,
        display: "flex",
        justifyContent: "center",
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize,
          fontWeight: 400,
          color,
          textAlign: "center",
          maxWidth: 700,
          lineHeight: 1.5,
        }}
      >
        {text}
      </div>
    </div>
  );
};

export default InsightText;
