import React from "react";
import { interpolate, Easing } from "remotion";
import {
  PANEL_BG,
  TEXT_COLOR,
  AMBER_ACCENT,
  PROMPT_X,
  PROMPT_Y,
  PROMPT_WIDTH,
  PANEL_RADIUS,
  PANEL_PADDING,
  HEADER_FONT_SIZE,
  HEADER_LETTER_SPACING,
  PROMPT_TEXT_SIZE,
  PROMPT_FADE_DURATION,
  PROMPT_LINES,
  MORPH_START,
  MORPH_DURATION,
} from "./constants";

/**
 * Left panel: a compact prompt document with amber aura.
 * Receives `localFrame` = frame relative to its Sequence start.
 */
interface PromptDocumentProps {
  localFrame: number;
  globalFrame: number;
}

export const PromptDocument: React.FC<PromptDocumentProps> = ({
  localFrame,
  globalFrame,
}) => {
  // Panel fade-in
  const panelOpacity = interpolate(
    localFrame,
    [0, PROMPT_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Slide in from left
  const slideX = interpolate(
    localFrame,
    [0, PROMPT_FADE_DURATION],
    [-40, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Aura builds up over slightly longer than fade
  const auraOpacity = interpolate(
    localFrame,
    [0, PROMPT_FADE_DURATION + 15],
    [0, 0.15],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Lines populate progressively
  const linesVisible = Math.min(
    PROMPT_LINES.length,
    Math.floor(
      interpolate(
        localFrame,
        [5, PROMPT_FADE_DURATION + 40],
        [0, PROMPT_LINES.length],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    )
  );

  // Morph effect: subtle glow intensification when morph begins
  const morphProgress =
    globalFrame >= MORPH_START
      ? interpolate(
          globalFrame,
          [MORPH_START, MORPH_START + MORPH_DURATION],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
        )
      : 0;

  const morphAuraIntensity = 0.15 + morphProgress * 0.2;
  const morphBlurRadius = 20 + morphProgress * 15;

  const containerHeight = PANEL_PADDING * 2 + 28 + PROMPT_LINES.length * 22;

  return (
    <div
      style={{
        position: "absolute",
        left: PROMPT_X + slideX,
        top: PROMPT_Y,
        width: PROMPT_WIDTH,
        height: containerHeight,
        opacity: panelOpacity,
      }}
    >
      {/* Amber aura glow */}
      <div
        style={{
          position: "absolute",
          inset: -20,
          borderRadius: PANEL_RADIUS + 20,
          boxShadow: `0 0 ${morphBlurRadius}px ${Math.round(morphBlurRadius * 0.6)}px ${AMBER_ACCENT}`,
          opacity: globalFrame >= MORPH_START ? morphAuraIntensity : auraOpacity,
          pointerEvents: "none",
        }}
      />

      {/* Panel background */}
      <div
        style={{
          position: "relative",
          width: "100%",
          height: "100%",
          backgroundColor: PANEL_BG,
          borderRadius: PANEL_RADIUS,
          padding: PANEL_PADDING,
          boxSizing: "border-box",
          overflow: "hidden",
        }}
      >
        {/* Header */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: HEADER_FONT_SIZE,
            fontWeight: 700,
            color: AMBER_ACCENT,
            letterSpacing: HEADER_LETTER_SPACING,
            marginBottom: 16,
          }}
        >
          PROMPT
        </div>

        {/* Prompt text lines */}
        {PROMPT_LINES.map((line, i) => {
          const isVisible = i < linesVisible;
          const isHeader = line.startsWith("#");
          return (
            <div
              key={i}
              style={{
                fontFamily: "Inter, sans-serif",
                fontSize: PROMPT_TEXT_SIZE,
                fontWeight: isHeader ? 600 : 400,
                color: isHeader ? AMBER_ACCENT : TEXT_COLOR,
                opacity: isVisible ? 0.95 : 0,
                lineHeight: "22px",
                height: 22,
                whiteSpace: "nowrap",
                overflow: "hidden",
                transition: "none",
              }}
            >
              {line || "\u00A0"}
            </div>
          );
        })}
      </div>
    </div>
  );
};

export default PromptDocument;
