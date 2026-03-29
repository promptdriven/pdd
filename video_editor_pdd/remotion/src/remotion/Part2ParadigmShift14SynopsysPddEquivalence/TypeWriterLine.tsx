import React, { useMemo } from "react";
import { useCurrentFrame } from "remotion";
import {
  FONT_FAMILY,
  MAIN_FONT_SIZE,
  CHAR_DELAY,
  ARROW_CHAR,
  ARROW_COLOR,
  CANVAS_WIDTH,
} from "./constants";
import type { TextSegment } from "./constants";

interface TypeWriterLineProps {
  segments: TextSegment[];
  startFrame: number;
  y: number;
}

interface CharInfo {
  char: string;
  color: string;
  weight: number;
  globalIndex: number;
}

export const TypeWriterLine: React.FC<TypeWriterLineProps> = ({
  segments,
  startFrame,
  y,
}) => {
  const frame = useCurrentFrame();

  // Build a flat list of characters with their styles
  const chars: CharInfo[] = useMemo(() => {
    const result: CharInfo[] = [];
    let idx = 0;
    for (const seg of segments) {
      for (const char of seg.text) {
        result.push({
          char,
          color: char === ARROW_CHAR ? ARROW_COLOR : seg.color,
          weight: seg.weight,
          globalIndex: idx,
        });
        idx++;
      }
    }
    return result;
  }, [segments]);

  const elapsed = frame - startFrame;
  // +1 so the first character is visible on the start frame
  const visibleCount = Math.max(0, Math.floor(elapsed / CHAR_DELAY) + 1);

  return (
    <div
      style={{
        position: "absolute",
        top: y,
        left: 0,
        width: CANVAS_WIDTH,
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        fontFamily: FONT_FAMILY,
        fontSize: MAIN_FONT_SIZE,
        whiteSpace: "pre",
      }}
    >
      {chars.map((c, i) => (
        <span
          key={i}
          style={{
            color: c.color,
            fontWeight: c.weight,
            opacity: i < visibleCount ? 1 : 0,
          }}
        >
          {c.char}
        </span>
      ))}
    </div>
  );
};
