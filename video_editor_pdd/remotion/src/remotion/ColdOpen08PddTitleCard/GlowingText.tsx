import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

/**
 * Animated text block that fades/slides in with an optional glow effect.
 */

interface GlowingTextProps {
  text: string;
  fontSize: number;
  color: string;
  glowColor: string;
  enterStart: number;
  enterEnd: number;
  offsetY?: number;
  fontWeight?: number;
  letterSpacing?: number;
  textTransform?: React.CSSProperties["textTransform"];
}

export const GlowingText: React.FC<GlowingTextProps> = ({
  text,
  fontSize,
  color,
  glowColor,
  enterStart,
  enterEnd,
  offsetY = 0,
  fontWeight = 700,
  letterSpacing = 0,
  textTransform = "none",
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [enterStart, enterEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(3)),
  });

  const translateY = interpolate(frame, [enterStart, enterEnd], [24, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(3)),
  });

  // Subtle glow pulse after entry
  const glowIntensity =
    frame > enterEnd
      ? interpolate(
          Math.sin(((frame - enterEnd) / 60) * Math.PI * 2),
          [-1, 1],
          [0.5, 1],
        )
      : interpolate(frame, [enterStart, enterEnd], [0, 0.7], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        });

  return (
    <div
      style={{
        opacity,
        transform: `translateY(${translateY + offsetY}px)`,
        fontSize,
        fontWeight,
        fontFamily: "'Inter', 'Helvetica Neue', Arial, sans-serif",
        color,
        letterSpacing,
        textTransform,
        textShadow: `0 0 ${30 * glowIntensity}px ${glowColor}, 0 0 ${60 * glowIntensity}px ${glowColor}`,
        whiteSpace: "nowrap",
        textAlign: "center",
        lineHeight: 1.1,
      }}
    >
      {text}
    </div>
  );
};

export default GlowingText;
