import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MONO_FONT,
  CODE_FONT_SIZE,
  LINE_NUMBER_SIZE,
  LINE_HEIGHT,
  GUTTER_WIDTH,
  GUTTER_INDICATOR_WIDTH,
  TEXT_COLOR,
  LINE_NUMBER_COLOR,
  ACCENT_AMBER,
} from "./constants";

export interface PromptLineProps {
  lineNumber: number;
  text: string;
  isHighlighted: boolean;
  /** Frame at which this line's gutter indicator starts animating */
  gutterAnimStartFrame: number;
  /** Y offset within the content area */
  yOffset: number;
  /** Whether this line is visible (has been revealed) */
  isVisible: boolean;
}

export const PromptLine: React.FC<PromptLineProps> = ({
  lineNumber,
  text,
  isHighlighted,
  gutterAnimStartFrame,
  yOffset,
  isVisible,
}) => {
  const frame = useCurrentFrame();

  if (!isVisible) return null;

  // Gutter indicator opacity — fades in over 4 frames with easeOut quad
  const gutterOpacity = interpolate(
    frame,
    [gutterAnimStartFrame, gutterAnimStartFrame + 4],
    [0, 0.5],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Highlighted edge-case lines get brighter gutter
  const gutterFinalOpacity = isHighlighted
    ? gutterOpacity * 1.6 // up to 0.8
    : gutterOpacity;

  // Text color slightly brighter for highlighted sections
  const lineTextColor = isHighlighted ? "#E2E8F0" : TEXT_COLOR;

  return (
    <div
      style={{
        position: "absolute",
        top: yOffset,
        left: 0,
        right: 0,
        height: LINE_HEIGHT,
        display: "flex",
        alignItems: "center",
      }}
    >
      {/* Gutter indicator bar */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 2,
          width: GUTTER_INDICATOR_WIDTH,
          height: LINE_HEIGHT - 4,
          backgroundColor: ACCENT_AMBER,
          opacity: gutterFinalOpacity,
          borderRadius: 1,
        }}
      />

      {/* Line number */}
      <div
        style={{
          width: GUTTER_WIDTH,
          textAlign: "right",
          paddingRight: 12,
          fontFamily: MONO_FONT,
          fontSize: LINE_NUMBER_SIZE,
          color: LINE_NUMBER_COLOR,
          opacity: 0.4,
          userSelect: "none",
          flexShrink: 0,
        }}
      >
        {lineNumber}
      </div>

      {/* Code text */}
      <div
        style={{
          fontFamily: MONO_FONT,
          fontSize: CODE_FONT_SIZE,
          color: lineTextColor,
          opacity: 0.9,
          whiteSpace: "pre",
          overflow: "hidden",
          textOverflow: "ellipsis",
          paddingLeft: 8,
        }}
      >
        {text}
      </div>
    </div>
  );
};
