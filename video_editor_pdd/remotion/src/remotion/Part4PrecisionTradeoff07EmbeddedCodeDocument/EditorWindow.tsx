import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  EDITOR_X,
  EDITOR_Y,
  EDITOR_WIDTH,
  EDITOR_HEIGHT,
  TITLE_BAR_HEIGHT,
  TITLE_BAR_COLOR,
  EDITOR_BG,
  FILENAME,
  TITLE_TEXT_COLOR,
  LINE_NUMBER_COLOR,
  LINE_GUTTER_WIDTH,
  NL_TEXT_COLOR,
  NL_GLOW_COLOR,
  CODE_TEXT_COLOR,
  CODE_BLOCK_BG,
  CODE_BORDER_OPACITY,
  CODE_BORDER_WIDTH,
  FONT_MONO,
  FONT_SANS,
  NATURAL_LANGUAGE_1,
  CODE_LINES,
  NATURAL_LANGUAGE_2,
  LINE_HEIGHT,
  CONTENT_START_Y,
  EDITOR_APPEAR_START,
  EDITOR_APPEAR_END,
  NL1_TYPE_START,
  CODE_BG_START,
  CODE_TYPE_START,
  NL2_TYPE_START,
} from "./constants";

const CHARS_PER_FRAME = 2;

function getTypedText(text: string, frame: number, startFrame: number): string {
  const elapsed = frame - startFrame;
  if (elapsed <= 0) return "";
  const charCount = Math.min(Math.floor(elapsed * CHARS_PER_FRAME), text.length);
  return text.substring(0, charCount);
}

function getLineStartFrame(
  lines: string[],
  sectionStartFrame: number
): number[] {
  const starts: number[] = [];
  let currentFrame = sectionStartFrame;
  for (const line of lines) {
    starts.push(currentFrame);
    currentFrame += Math.ceil(line.length / CHARS_PER_FRAME) + 2; // +2 frame gap between lines
  }
  return starts;
}

export const EditorWindow: React.FC = () => {
  const frame = useCurrentFrame();

  // Editor appear animation
  const editorOpacity = interpolate(
    frame,
    [EDITOR_APPEAR_START, EDITOR_APPEAR_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const editorScale = interpolate(
    frame,
    [EDITOR_APPEAR_START, EDITOR_APPEAR_END],
    [0.95, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Line start frames for each section
  const nl1Starts = getLineStartFrame(NATURAL_LANGUAGE_1, NL1_TYPE_START);
  const codeStarts = getLineStartFrame(CODE_LINES, CODE_TYPE_START);
  const nl2Starts = getLineStartFrame(NATURAL_LANGUAGE_2, NL2_TYPE_START);

  // Code block background slide-in
  const codeBlockOpacity = interpolate(
    frame,
    [CODE_BG_START, CODE_BG_START + 15],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const codeBlockSlideX = interpolate(
    frame,
    [CODE_BG_START, CODE_BG_START + 15],
    [-20, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Code block Y position and height
  const codeBlockYStart = CONTENT_START_Y + NATURAL_LANGUAGE_1.length * LINE_HEIGHT;
  const codeBlockHeight = CODE_LINES.length * LINE_HEIGHT + 12;

  return (
    <div
      style={{
        position: "absolute",
        left: EDITOR_X,
        top: EDITOR_Y,
        width: EDITOR_WIDTH,
        height: EDITOR_HEIGHT,
        opacity: editorOpacity,
        transform: `scale(${editorScale})`,
        borderRadius: "8px 8px 4px 4px",
        overflow: "hidden",
        boxShadow: "0 20px 60px rgba(0,0,0,0.5)",
      }}
    >
      {/* Title bar */}
      <div
        style={{
          width: EDITOR_WIDTH,
          height: TITLE_BAR_HEIGHT,
          backgroundColor: TITLE_BAR_COLOR,
          display: "flex",
          alignItems: "center",
          paddingLeft: 16,
          gap: 8,
        }}
      >
        {/* Window dots */}
        <div
          style={{
            width: 10,
            height: 10,
            borderRadius: "50%",
            backgroundColor: "#EF4444",
            opacity: 0.7,
          }}
        />
        <div
          style={{
            width: 10,
            height: 10,
            borderRadius: "50%",
            backgroundColor: "#F59E0B",
            opacity: 0.7,
          }}
        />
        <div
          style={{
            width: 10,
            height: 10,
            borderRadius: "50%",
            backgroundColor: "#22C55E",
            opacity: 0.7,
          }}
        />
        <div
          style={{
            fontFamily: FONT_MONO,
            fontSize: 11,
            color: TITLE_TEXT_COLOR,
            opacity: 0.7,
            marginLeft: 12,
          }}
        >
          {FILENAME}
        </div>
      </div>

      {/* Editor body */}
      <div
        style={{
          width: EDITOR_WIDTH,
          height: EDITOR_HEIGHT - TITLE_BAR_HEIGHT,
          backgroundColor: EDITOR_BG,
          position: "relative",
          padding: "12px 0",
        }}
      >
        {/* Natural language section 1 */}
        {NATURAL_LANGUAGE_1.map((line, i) => {
          const lineNum = i + 1;
          const typed = getTypedText(line, frame, nl1Starts[i]);
          const isComplete = typed.length === line.length;
          const yPos = CONTENT_START_Y + i * LINE_HEIGHT;

          return (
            <div
              key={`nl1-${i}`}
              style={{
                position: "absolute",
                left: 0,
                top: yPos,
                width: EDITOR_WIDTH - 20,
                height: LINE_HEIGHT,
                display: "flex",
                alignItems: "center",
              }}
            >
              {/* Line number */}
              <div
                style={{
                  width: LINE_GUTTER_WIDTH,
                  textAlign: "right",
                  paddingRight: 12,
                  fontFamily: FONT_MONO,
                  fontSize: 10,
                  color: LINE_NUMBER_COLOR,
                  opacity: typed.length > 0 ? 0.25 : 0,
                }}
              >
                {lineNum}
              </div>
              {/* Text with glow */}
              <div
                style={{
                  fontFamily: FONT_SANS,
                  fontSize: 13,
                  color: NL_TEXT_COLOR,
                  opacity: 0.8,
                  fontWeight: i === 0 ? 700 : 400,
                  textShadow: isComplete
                    ? `0 0 20px ${NL_GLOW_COLOR}08`
                    : "none",
                  whiteSpace: "pre",
                }}
              >
                {typed}
              </div>
            </div>
          );
        })}

        {/* Code block background */}
        <div
          style={{
            position: "absolute",
            left: LINE_GUTTER_WIDTH + 8 + codeBlockSlideX,
            top: codeBlockYStart - 6,
            width: EDITOR_WIDTH - LINE_GUTTER_WIDTH - 30,
            height: codeBlockHeight,
            backgroundColor: CODE_BLOCK_BG,
            borderLeft: `${CODE_BORDER_WIDTH}px solid rgba(148, 163, 184, ${CODE_BORDER_OPACITY})`,
            borderRadius: 4,
            opacity: codeBlockOpacity,
          }}
        />

        {/* Code lines */}
        {CODE_LINES.map((line, i) => {
          const lineNum = NATURAL_LANGUAGE_1.length + i + 1;
          const typed = getTypedText(line, frame, codeStarts[i]);
          const yPos =
            CONTENT_START_Y + (NATURAL_LANGUAGE_1.length + i) * LINE_HEIGHT;

          return (
            <div
              key={`code-${i}`}
              style={{
                position: "absolute",
                left: 0,
                top: yPos,
                width: EDITOR_WIDTH - 20,
                height: LINE_HEIGHT,
                display: "flex",
                alignItems: "center",
              }}
            >
              <div
                style={{
                  width: LINE_GUTTER_WIDTH,
                  textAlign: "right",
                  paddingRight: 12,
                  fontFamily: FONT_MONO,
                  fontSize: 10,
                  color: LINE_NUMBER_COLOR,
                  opacity: typed.length > 0 ? 0.25 : 0,
                }}
              >
                {lineNum}
              </div>
              <div
                style={{
                  fontFamily: FONT_MONO,
                  fontSize: 11,
                  color: CODE_TEXT_COLOR,
                  opacity: 0.7,
                  whiteSpace: "pre",
                  paddingLeft: 8,
                }}
              >
                {typed}
              </div>
            </div>
          );
        })}

        {/* Natural language section 2 */}
        {NATURAL_LANGUAGE_2.map((line, i) => {
          const lineNum =
            NATURAL_LANGUAGE_1.length + CODE_LINES.length + i + 1;
          const typed = getTypedText(line, frame, nl2Starts[i]);
          const isComplete = typed.length === line.length;
          const yPos =
            CONTENT_START_Y +
            (NATURAL_LANGUAGE_1.length + CODE_LINES.length + i) * LINE_HEIGHT;

          return (
            <div
              key={`nl2-${i}`}
              style={{
                position: "absolute",
                left: 0,
                top: yPos,
                width: EDITOR_WIDTH - 20,
                height: LINE_HEIGHT,
                display: "flex",
                alignItems: "center",
              }}
            >
              <div
                style={{
                  width: LINE_GUTTER_WIDTH,
                  textAlign: "right",
                  paddingRight: 12,
                  fontFamily: FONT_MONO,
                  fontSize: 10,
                  color: LINE_NUMBER_COLOR,
                  opacity: typed.length > 0 ? 0.25 : 0,
                }}
              >
                {lineNum}
              </div>
              <div
                style={{
                  fontFamily: FONT_SANS,
                  fontSize: 13,
                  color: NL_TEXT_COLOR,
                  opacity: 0.8,
                  textShadow: isComplete
                    ? `0 0 20px ${NL_GLOW_COLOR}08`
                    : "none",
                  whiteSpace: "pre",
                }}
              >
                {typed}
              </div>
            </div>
          );
        })}
      </div>
    </div>
  );
};
