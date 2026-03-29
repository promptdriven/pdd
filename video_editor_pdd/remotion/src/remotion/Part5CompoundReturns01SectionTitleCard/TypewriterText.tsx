import React from "react";
import { useCurrentFrame } from "remotion";

interface TypewriterTextProps {
  text: string;
  charDelay: number;
  fontSize: number;
  fontWeight: number;
  color: string;
  y: number;
  offsetX?: number;
}

/**
 * Reveals text character-by-character.
 * Each character appears `charDelay` frames after the previous one.
 */
export const TypewriterText: React.FC<TypewriterTextProps> = ({
  text,
  charDelay,
  fontSize,
  fontWeight,
  color,
  y,
  offsetX = 0,
}) => {
  const frame = useCurrentFrame();
  const visibleChars = Math.min(
    text.length,
    Math.floor(frame / charDelay) + 1
  );
  const displayText = text.slice(0, visibleChars);

  return (
    <div
      style={{
        position: "absolute",
        top: y,
        left: 0,
        width: "100%",
        display: "flex",
        justifyContent: "center",
        transform: `translateX(${offsetX}px)`,
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize,
          fontWeight,
          color,
          letterSpacing: 2,
          lineHeight: 1,
          whiteSpace: "pre",
        }}
      >
        {displayText}
      </span>
    </div>
  );
};
