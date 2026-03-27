import React from "react";
import { useCurrentFrame } from "remotion";
import {
  FONT_FAMILY,
  LINE_FONT_SIZE,
  CENTER_X,
  CHAR_DELAY_FRAMES,
} from "./constants";
import type { TextSegment } from "./constants";

interface TypeWriterLineProps {
  segments: TextSegment[];
  y: number;
  startFrame: number;
}

/**
 * Renders a typewriter-style line with multiple styled segments.
 * Characters appear at CHAR_DELAY_FRAMES per character, linear.
 */
export const TypeWriterLine: React.FC<TypeWriterLineProps> = ({
  segments,
  y,
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const elapsed = frame - startFrame;

  if (elapsed < 0) return null;

  // Total character count across all segments
  const totalChars = segments.reduce((sum, s) => sum + s.text.length, 0);
  const charsToShow = Math.min(
    totalChars,
    Math.floor(elapsed / CHAR_DELAY_FRAMES)
  );

  // Build visible spans
  let charsRemaining = charsToShow;
  const spans: React.ReactNode[] = [];

  for (let i = 0; i < segments.length; i++) {
    const seg = segments[i];
    if (charsRemaining <= 0) break;

    const visibleCount = Math.min(seg.text.length, charsRemaining);
    const visibleText = seg.text.slice(0, visibleCount);
    charsRemaining -= visibleCount;

    spans.push(
      <span
        key={i}
        style={{
          color: seg.color,
          fontWeight: seg.fontWeight,
        }}
      >
        {visibleText}
      </span>
    );
  }

  return (
    <div
      style={{
        position: "absolute",
        top: y,
        left: 0,
        width: CENTER_X * 2,
        textAlign: "center",
        fontFamily: FONT_FAMILY,
        fontSize: LINE_FONT_SIZE,
        lineHeight: 1.4,
        whiteSpace: "pre",
      }}
    >
      {spans}
      {/* Blinking cursor while typing */}
      {charsToShow < totalChars && (
        <span
          style={{
            color: "#E2E8F0",
            opacity: Math.sin(elapsed * 0.3) > 0 ? 0.85 : 0,
          }}
        >
          |
        </span>
      )}
    </div>
  );
};
