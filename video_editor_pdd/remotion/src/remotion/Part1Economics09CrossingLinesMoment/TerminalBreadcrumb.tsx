import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  FONT_FAMILY,
  MONO_FONT,
  BLUE_LINE_COLOR,
  TERMINAL_START,
} from "./constants";

/**
 * TerminalBreadcrumb: Renders "pdd generate" in JetBrains Mono at
 * the bottom-right corner with very low opacity.
 */
export const TerminalBreadcrumb: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < TERMINAL_START) return null;

  const opacity = interpolate(
    frame,
    [TERMINAL_START, TERMINAL_START + 15],
    [0, 0.12],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  return (
    <AbsoluteFill>
      <div
        style={{
          position: "absolute",
          right: 120,
          bottom: 40,
          fontFamily: MONO_FONT,
          fontSize: 10,
          color: BLUE_LINE_COLOR,
          opacity,
          letterSpacing: 0.5,
        }}
      >
        pdd generate
      </div>
    </AbsoluteFill>
  );
};

export default TerminalBreadcrumb;
