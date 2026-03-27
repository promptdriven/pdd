import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  AMBER,
  TEAL,
  MOLD_CENTER_X,
  NOZZLE_TIP_Y,
  CAVITY_TOP,
  CAVITY_LEFT,
  PROMPT_TEXT,
  PHASE_TEXT_STREAM_START,
} from "./constants";

export const PromptTextStream: React.FC = () => {
  const frame = useCurrentFrame();

  // Number of characters visible (2 frames per character)
  const streamFrame = frame - PHASE_TEXT_STREAM_START;
  if (streamFrame < 0) return null;

  const charsVisible = Math.min(
    Math.floor(streamFrame / 2),
    PROMPT_TEXT.length
  );

  const visibleText = PROMPT_TEXT.slice(0, charsVisible);

  // Split visible text into characters for individual coloring
  // Characters near the nozzle are amber, deeper in cavity become teal
  const charElements: React.ReactNode[] = [];
  const charsPerLine = 50;
  const lineHeight = 16;
  const startX = CAVITY_LEFT + 10;
  const startY = CAVITY_TOP + 20;

  for (let i = 0; i < visibleText.length; i++) {
    const lineIndex = Math.floor(i / charsPerLine);
    const colIndex = i % charsPerLine;

    // Transition from amber to teal based on how deep the character is
    const depthRatio = interpolate(
      lineIndex * charsPerLine + colIndex,
      [0, PROMPT_TEXT.length * 0.3, PROMPT_TEXT.length],
      [0, 0.3, 1],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      }
    );

    // Once character has been "in" for a while, it transforms to liquid
    const charAge = streamFrame - i * 2;
    const liquidTransform = interpolate(charAge, [0, 30], [0, 1], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.sin),
    });

    // Blend amber → teal
    const finalBlend = Math.min(depthRatio + liquidTransform * 0.5, 1);

    charElements.push(
      <tspan
        key={i}
        x={startX + colIndex * 7.2}
        y={startY + lineIndex * lineHeight}
        fill={finalBlend > 0.5 ? TEAL : AMBER}
        opacity={interpolate(finalBlend, [0, 0.5, 1], [1, 0.9, 0.8], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })}
      >
        {visibleText[i]}
      </tspan>
    );
  }

  // Cursor blink at the end of text
  const cursorLine = Math.floor(charsVisible / charsPerLine);
  const cursorCol = charsVisible % charsPerLine;
  const cursorVisible = Math.floor(frame / 8) % 2 === 0;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Streaming text from nozzle into cavity */}
      {/* Flow line from nozzle to text area */}
      {charsVisible > 0 && (
        <line
          x1={MOLD_CENTER_X}
          y1={NOZZLE_TIP_Y + 4}
          x2={MOLD_CENTER_X}
          y2={startY - 5}
          stroke={AMBER}
          strokeWidth={2}
          opacity={interpolate(
            streamFrame,
            [0, 10, PROMPT_TEXT.length * 2, PROMPT_TEXT.length * 2 + 20],
            [0, 0.6, 0.6, 0],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          )}
        />
      )}

      <text
        fontFamily="'JetBrains Mono', monospace"
        fontSize={12}
      >
        {charElements}
      </text>

      {/* Cursor */}
      {cursorVisible && charsVisible < PROMPT_TEXT.length && (
        <rect
          x={startX + cursorCol * 7.2}
          y={startY + cursorLine * lineHeight - 12}
          width={7}
          height={14}
          fill={AMBER}
          opacity={0.8}
        />
      )}
    </svg>
  );
};
