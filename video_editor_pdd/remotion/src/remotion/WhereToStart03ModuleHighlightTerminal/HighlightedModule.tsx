import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  GREEN_ACCENT,
  CODE_FILE_X,
  CODE_FILE_Y,
  MODULE_WIDTH,
  MODULE_HEIGHT,
  CODE_LINES,
  HIGHLIGHT_START,
  HIGHLIGHT_DURATION,
  DESAT_START,
  DESAT_DURATION,
} from "./constants";

/**
 * The highlighted auth_handler.py module with green border glow.
 * Desaturates to gray after particle flow begins.
 */
export const HighlightedModule: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade-in progress for highlight appearance
  const highlightProgress = interpolate(
    frame,
    [HIGHLIGHT_START, HIGHLIGHT_START + HIGHLIGHT_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Glow opacity
  const glowOpacity = highlightProgress * 0.2;

  // Desaturation: code file goes gray
  const desaturation = interpolate(
    frame,
    [DESAT_START, DESAT_START + DESAT_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Border color transitions from green to gray during desaturation
  const borderRgb = lerpRgb(
    hexToRgb(GREEN_ACCENT),
    hexToRgb("#64748B"),
    desaturation
  );
  const borderColor = `rgba(${borderRgb.r}, ${borderRgb.g}, ${borderRgb.b}, ${highlightProgress})`;

  const labelRgb = lerpRgb(
    hexToRgb(GREEN_ACCENT),
    hexToRgb("#64748B"),
    desaturation
  );
  const labelColor = `rgba(${labelRgb.r}, ${labelRgb.g}, ${labelRgb.b}, ${highlightProgress})`;

  const codeLineRgb = lerpRgb(
    hexToRgb("#8BA4BE"),
    hexToRgb("#555F6B"),
    desaturation
  );

  const glowColor =
    desaturation > 0
      ? `rgba(100, 116, 139, ${glowOpacity})`
      : `rgba(90, 170, 110, ${glowOpacity})`;

  return (
    <div
      style={{
        position: "absolute",
        left: CODE_FILE_X - MODULE_WIDTH / 2,
        top: CODE_FILE_Y - MODULE_HEIGHT / 2,
        width: MODULE_WIDTH,
        height: MODULE_HEIGHT,
        borderRadius: 4,
        border: `2px solid ${borderColor}`,
        backgroundColor: "rgba(10, 15, 26, 0.9)",
        boxShadow: `0 0 15px ${glowColor}`,
        overflow: "hidden",
        padding: 12,
        filter: desaturation > 0 ? `saturate(${1 - desaturation * 0.8})` : undefined,
      }}
    >
      {/* File label */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 600,
          color: labelColor,
          marginBottom: 10,
        }}
      >
        auth_handler.py
      </div>

      {/* Fake code lines */}
      {CODE_LINES.map((line, i) => (
        <div
          key={i}
          style={{
            height: 4,
            width: `${line.width * 80}%`,
            marginLeft: line.indent * 16,
            marginBottom: 7,
            backgroundColor: `rgba(${codeLineRgb.r}, ${codeLineRgb.g}, ${codeLineRgb.b}, ${0.5 * highlightProgress})`,
            borderRadius: 2,
          }}
        />
      ))}
    </div>
  );
};

function hexToRgb(hex: string): { r: number; g: number; b: number } {
  const clean = hex.replace("#", "");
  return {
    r: parseInt(clean.substring(0, 2), 16),
    g: parseInt(clean.substring(2, 4), 16),
    b: parseInt(clean.substring(4, 6), 16),
  };
}

function lerpRgb(
  from: { r: number; g: number; b: number },
  to: { r: number; g: number; b: number },
  t: number
): { r: number; g: number; b: number } {
  return {
    r: Math.round(from.r + (to.r - from.r) * t),
    g: Math.round(from.g + (to.g - from.g) * t),
    b: Math.round(from.b + (to.b - from.b) * t),
  };
}

export default HighlightedModule;
