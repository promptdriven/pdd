import React from "react";
import { useCurrentFrame } from "remotion";
import {
  TITLE_COLOR,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_LETTER_SPACING,
  TITLE_TEXT,
  FRAMES_PER_CHAR,
} from "./constants";

interface TypewriterTextProps {
  text?: string;
  fontSize?: number;
  fontWeight?: number;
  color?: string;
  letterSpacing?: number;
  framesPerChar?: number;
  y?: number;
}

export const TypewriterText: React.FC<TypewriterTextProps> = ({
  text = TITLE_TEXT,
  fontSize = TITLE_FONT_SIZE,
  fontWeight = TITLE_FONT_WEIGHT,
  color = TITLE_COLOR,
  letterSpacing = TITLE_LETTER_SPACING,
  framesPerChar = FRAMES_PER_CHAR,
  y = 0,
}) => {
  const frame = useCurrentFrame();
  const charsVisible = Math.min(
    Math.floor(frame / framesPerChar),
    text.length
  );
  const displayedText = text.slice(0, charsVisible);
  const showCursor = charsVisible < text.length;

  return (
    <div
      style={{
        position: "absolute",
        top: y,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize,
          fontWeight,
          color,
          letterSpacing,
          whiteSpace: "pre",
        }}
      >
        {displayedText}
        {showCursor && (
          <span
            style={{
              display: "inline-block",
              width: 2,
              height: fontSize * 0.75,
              backgroundColor: color,
              marginLeft: 1,
              verticalAlign: "middle",
              opacity: 0.7,
            }}
          />
        )}
      </span>
    </div>
  );
};
