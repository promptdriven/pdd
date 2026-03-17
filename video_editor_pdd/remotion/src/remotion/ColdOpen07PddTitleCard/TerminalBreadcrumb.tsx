import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TERMINAL_TEXT,
  TERMINAL_FONT_SIZE,
  TERMINAL_COLOR,
  TERMINAL_OPACITY,
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_START_FRAME,
  TERMINAL_FADE_DURATION,
  CODE_FONT_FAMILY,
} from "./constants";

/**
 * Terminal breadcrumb "pdd generate" in bottom-right corner.
 * Nearly invisible at 0.15 opacity — discoverable, not attention-grabbing.
 * Fades in at frame 80 over 20 frames.
 */
export const TerminalBreadcrumb: React.FC = () => {
  const frame = useCurrentFrame();

  const localFrame = frame - TERMINAL_START_FRAME;
  if (localFrame < 0) return null;

  const opacity = interpolate(
    localFrame,
    [0, TERMINAL_FADE_DURATION],
    [0, TERMINAL_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: TERMINAL_Y,
        left: TERMINAL_X,
        fontFamily: CODE_FONT_FAMILY,
        fontSize: TERMINAL_FONT_SIZE,
        color: TERMINAL_COLOR,
        opacity,
        pointerEvents: "none",
      }}
    >
      {TERMINAL_TEXT}
    </div>
  );
};
