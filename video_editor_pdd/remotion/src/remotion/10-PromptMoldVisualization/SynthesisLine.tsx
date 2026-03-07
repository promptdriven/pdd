import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  FONT_FAMILY,
  SYNTHESIS_FONT_SIZE,
  SYNTHESIS_DEFAULT_COLOR,
  SYNTHESIS_HIGHLIGHT_COLOR,
  SYNTHESIS_Y,
  SYNTH_ENTER,
  SYNTH_PHRASE1_START,
  SYNTH_PHRASE2_START,
  SYNTH_PHRASE3_START,
  PROMPT_BORDER,
  CODE_BORDER,
  TESTS_BORDER,
} from "./constants";

interface Phrase {
  text: string;
  highlightStart: number;
  glowColor: string;
}

const PHRASES: Phrase[] = [
  { text: "Design the specification.", highlightStart: SYNTH_PHRASE1_START, glowColor: PROMPT_BORDER },
  { text: "Generate the implementation.", highlightStart: SYNTH_PHRASE2_START, glowColor: CODE_BORDER },
  { text: "Verify automatically.", highlightStart: SYNTH_PHRASE3_START, glowColor: TESTS_BORDER },
];

export const SynthesisLine: React.FC = () => {
  const frame = useCurrentFrame();

  // Overall synthesis line fade-in
  const lineOpacity = interpolate(
    frame,
    [SYNTH_ENTER, SYNTH_ENTER + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  if (lineOpacity <= 0) return null;

  return (
    <div
      style={{
        position: "absolute",
        top: SYNTHESIS_Y,
        left: 0,
        width: 1920,
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        gap: 16,
        opacity: lineOpacity,
      }}
    >
      {PHRASES.map((phrase, i) => {
        const highlightProgress = interpolate(
          frame,
          [phrase.highlightStart, phrase.highlightStart + 15],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        );

        const isActive = highlightProgress > 0;
        const color = isActive
          ? interpolateColor(SYNTHESIS_DEFAULT_COLOR, SYNTHESIS_HIGHLIGHT_COLOR, highlightProgress)
          : SYNTHESIS_DEFAULT_COLOR;

        const textShadow = isActive
          ? `0 0 ${12 * highlightProgress}px ${phrase.glowColor}`
          : "none";

        return (
          <React.Fragment key={i}>
            {i > 0 && (
              <span
                style={{
                  fontFamily: FONT_FAMILY,
                  fontSize: SYNTHESIS_FONT_SIZE,
                  fontWeight: 600,
                  color: SYNTHESIS_DEFAULT_COLOR,
                }}
              >
                —
              </span>
            )}
            <span
              style={{
                fontFamily: FONT_FAMILY,
                fontSize: SYNTHESIS_FONT_SIZE,
                fontWeight: 600,
                color,
                textShadow,
                transition: "none",
              }}
            >
              {phrase.text}
            </span>
          </React.Fragment>
        );
      })}
    </div>
  );
};

/**
 * Simple hex color interpolation between two hex colors.
 */
function interpolateColor(from: string, to: string, t: number): string {
  const fromRgb = hexToRgb(from);
  const toRgb = hexToRgb(to);
  const r = Math.round(fromRgb.r + (toRgb.r - fromRgb.r) * t);
  const g = Math.round(fromRgb.g + (toRgb.g - fromRgb.g) * t);
  const b = Math.round(fromRgb.b + (toRgb.b - fromRgb.b) * t);
  return `rgb(${r}, ${g}, ${b})`;
}

function hexToRgb(hex: string): { r: number; g: number; b: number } {
  const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  if (!result) return { r: 148, g: 163, b: 184 }; // fallback to slate-400
  return {
    r: parseInt(result[1], 16),
    g: parseInt(result[2], 16),
    b: parseInt(result[3], 16),
  };
}
