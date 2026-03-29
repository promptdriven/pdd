import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

interface QuadrantFillProps {
  /** Pixel position of the quadrant's top-left corner */
  quadrantLeft: number;
  quadrantTop: number;
  /** Size of each cell */
  cellSize: number;
  /** The accent color for the quadrant */
  accentColor: string;
  /** Background fill opacity target */
  fillOpacity: number;
  /** Border glow opacity target */
  glowOpacity: number;
  /** Label text displayed in the quadrant center */
  labelText: string;
  /** Label color */
  labelColor: string;
  /** Label font size */
  labelSize: number;
  /** Frame at which this quadrant starts animating (relative to Sequence) */
  animateInDuration: number;
  /** Frames per character for type-in effect */
  framesPerChar: number;
}

const QuadrantFill: React.FC<QuadrantFillProps> = ({
  quadrantLeft,
  quadrantTop,
  cellSize,
  accentColor,
  fillOpacity,
  glowOpacity,
  labelText,
  labelColor,
  labelSize,
  animateInDuration,
  framesPerChar,
}) => {
  const frame = useCurrentFrame();

  // Fill opacity animation
  const currentFillOpacity = interpolate(
    frame,
    [0, animateInDuration],
    [0, fillOpacity],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Glow opacity animation
  const currentGlowOpacity = interpolate(
    frame,
    [0, animateInDuration],
    [0, glowOpacity],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Type-in effect for label
  const totalChars = labelText.length;
  const typeStartFrame = animateInDuration * 0.5;
  const charsVisible = Math.floor(
    interpolate(
      frame,
      [typeStartFrame, typeStartFrame + totalChars * framesPerChar],
      [0, totalChars],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      }
    )
  );
  const visibleText = labelText.slice(0, charsVisible);

  // Pulsing glow effect (subtle, after fill-in completes)
  const pulsePhase = interpolate(
    frame,
    [animateInDuration, animateInDuration + 120],
    [0, Math.PI * 2],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "extend",
    }
  );
  const pulseMultiplier =
    frame > animateInDuration ? 1 + Math.sin(pulsePhase) * 0.1 : 1;

  return (
    <div
      style={{
        position: "absolute",
        left: quadrantLeft,
        top: quadrantTop,
        width: cellSize,
        height: cellSize,
      }}
    >
      {/* Background fill */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: cellSize,
          height: cellSize,
          backgroundColor: accentColor,
          opacity: currentFillOpacity * pulseMultiplier,
        }}
      />

      {/* Border glow */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: cellSize,
          height: cellSize,
          border: `2px solid ${accentColor}`,
          opacity: currentGlowOpacity * pulseMultiplier,
          boxShadow: `inset 0 0 30px ${accentColor}40, 0 0 20px ${accentColor}30`,
        }}
      />

      {/* Label text */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: cellSize,
          height: cellSize,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: labelSize,
          fontWeight: 700,
          color: labelColor,
          textAlign: "center",
          padding: 20,
          lineHeight: 1.4,
        }}
      >
        {visibleText}
        {charsVisible < totalChars && charsVisible > 0 && (
          <span
            style={{
              opacity: frame % 10 < 5 ? 1 : 0.3,
              marginLeft: 1,
            }}
          >
            |
          </span>
        )}
      </div>
    </div>
  );
};

export default QuadrantFill;
