import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface QuadrantFillProps {
  /** Pixel position of the quadrant's top-left corner */
  x: number;
  y: number;
  size: number;
  color: string;
  fillOpacity: number;
  glowOpacity: number;
  label: string;
  labelColor: string;
  labelSize: number;
  /** Frame at which illumination starts (relative to Sequence, so use absolute frame) */
  animStart: number;
  animEnd: number;
}

export const QuadrantFill: React.FC<QuadrantFillProps> = ({
  x,
  y,
  size,
  color,
  fillOpacity,
  glowOpacity,
  label,
  labelColor,
  labelSize,
  animStart,
  animEnd,
}) => {
  const frame = useCurrentFrame();

  // Fill fade-in
  const fill = interpolate(frame, [animStart, animEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Typewriter effect: 2 frames per character
  const charsVisible = Math.floor(
    interpolate(frame, [animStart + 10, animStart + 10 + label.length * 2], [0, label.length], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    })
  );

  const displayedText = label.slice(0, charsVisible);

  // Subtle pulsing glow after fully revealed
  const pulsePhase = Math.max(0, frame - animEnd);
  const pulse = 1 + 0.08 * Math.sin((pulsePhase / 30) * Math.PI * 2);

  return (
    <>
      {/* Background fill */}
      <div
        style={{
          position: "absolute",
          left: x,
          top: y,
          width: size,
          height: size,
          backgroundColor: color,
          opacity: fillOpacity * fill,
        }}
      />

      {/* Glow border */}
      <div
        style={{
          position: "absolute",
          left: x,
          top: y,
          width: size,
          height: size,
          boxShadow: `inset 0 0 ${30 * fill * pulse}px ${color}`,
          opacity: glowOpacity * fill,
          pointerEvents: "none",
        }}
      />

      {/* Outer glow */}
      <div
        style={{
          position: "absolute",
          left: x - 4,
          top: y - 4,
          width: size + 8,
          height: size + 8,
          boxShadow: `0 0 ${20 * fill * pulse}px ${8 * fill}px ${color}`,
          opacity: glowOpacity * fill * 0.5,
          pointerEvents: "none",
        }}
      />

      {/* Label */}
      <div
        style={{
          position: "absolute",
          left: x,
          top: y,
          width: size,
          height: size,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: labelSize,
          fontWeight: 700,
          color: labelColor,
          whiteSpace: "nowrap",
          pointerEvents: "none",
        }}
      >
        {displayedText}
        {charsVisible < label.length && charsVisible > 0 && (
          <span
            style={{
              opacity: Math.sin(frame * 0.3) > 0 ? 1 : 0,
              marginLeft: 1,
            }}
          >
            |
          </span>
        )}
      </div>
    </>
  );
};

export default QuadrantFill;
