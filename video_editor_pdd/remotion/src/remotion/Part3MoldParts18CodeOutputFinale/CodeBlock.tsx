import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CODE_BLOCK_WIDTH,
  CODE_BLOCK_HEIGHT,
  CODE_BG_COLOR,
  CODE_BORDER_COLOR,
  CODE_BORDER_FADED,
  CODE_FONT_SIZE,
  CODE_GLOW_FADE_START,
  CODE_GLOW_FADE_END,
  CODE_GLOW_FROM,
  CODE_GLOW_TO,
  CODE_DIM_START,
  CODE_DIM_END,
  CODE_TEXT_FROM,
  CODE_TEXT_TO,
  CODE_FADE_IN_DURATION,
  PYTHON_CODE,
} from "./constants";
import type { CodeLine } from "./constants";

/**
 * Syntax-highlighted code block that fades in, then dims
 * while its glow fades out.
 */
export const CodeBlock: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in over first 15 frames
  const fadeIn = interpolate(frame, [0, CODE_FADE_IN_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Glow fades from 0.2 → 0 over frames 20–40
  const glowOpacity = interpolate(
    frame,
    [CODE_GLOW_FADE_START, CODE_GLOW_FADE_END],
    [CODE_GLOW_FROM, CODE_GLOW_TO],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // Text dims from 1.0 → 0.4 over frames 20–40
  const textOpacity = interpolate(
    frame,
    [CODE_DIM_START, CODE_DIM_END],
    [CODE_TEXT_FROM, CODE_TEXT_TO],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // Border transitions from active to faded
  const borderProgress = interpolate(
    frame,
    [CODE_GLOW_FADE_START, CODE_GLOW_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const currentBorder =
    borderProgress < 0.5 ? CODE_BORDER_COLOR : CODE_BORDER_FADED;

  return (
    <div
      style={{
        position: "absolute",
        left: "50%",
        top: 650,
        transform: "translateX(-50%)",
        width: CODE_BLOCK_WIDTH,
        height: CODE_BLOCK_HEIGHT,
        backgroundColor: CODE_BG_COLOR,
        border: `1px solid ${currentBorder}`,
        borderRadius: 8,
        padding: "16px 20px",
        opacity: fadeIn,
        boxShadow:
          glowOpacity > 0
            ? `0 0 15px rgba(56, 189, 248, ${glowOpacity}), 0 0 30px rgba(56, 189, 248, ${glowOpacity * 0.5})`
            : "none",
        overflow: "hidden",
      }}
    >
      <pre
        style={{
          margin: 0,
          padding: 0,
          fontFamily: "'JetBrains Mono', 'Fira Code', 'Cascadia Code', monospace",
          fontSize: CODE_FONT_SIZE,
          lineHeight: 1.65,
          opacity: textOpacity,
        }}
      >
        {PYTHON_CODE.map((line: CodeLine, lineIdx: number) => (
          <div key={lineIdx} style={{ minHeight: CODE_FONT_SIZE * 1.65 }}>
            {line.map((token, tokenIdx) => (
              <span key={tokenIdx} style={{ color: token.color }}>
                {token.text}
              </span>
            ))}
          </div>
        ))}
      </pre>
    </div>
  );
};

export default CodeBlock;
