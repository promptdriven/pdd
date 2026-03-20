import React from "react";
import { useCurrentFrame, useVideoConfig } from "remotion";
import {
  CURSOR_COLOR,
  CURSOR_WIDTH,
  CURSOR_HEIGHT,
  CURSOR_ON_MS,
  CURSOR_OFF_MS,
  CODE_X_START,
  CODE_Y_START,
} from "./constants";

/**
 * A blinking editor cursor. At frames 120-150 the final blink is
 * held longer (800ms on) to create the "deliberate pause" effect.
 */
export const BlinkingCursor: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const msPerFrame = 1000 / fps;
  const currentMs = frame * msPerFrame;

  // After frame 120 the cursor holds ON for 800ms then OFF for 530ms
  const isDeliberatePhase = frame >= 120;
  const onMs = isDeliberatePhase ? 800 : CURSOR_ON_MS;
  const offMs = isDeliberatePhase ? CURSOR_OFF_MS : CURSOR_OFF_MS;
  const cycleMs = onMs + offMs;

  // Calculate phase-relative time
  const phaseStartMs = isDeliberatePhase ? 120 * msPerFrame : 0;
  const elapsed = currentMs - phaseStartMs;
  const withinCycle = ((elapsed % cycleMs) + cycleMs) % cycleMs;
  const isVisible = withinCycle < onMs;

  return (
    <div
      style={{
        position: "absolute",
        left: CODE_X_START,
        top: CODE_Y_START + 3, // slight vertical offset to center in line
        width: CURSOR_WIDTH,
        height: CURSOR_HEIGHT,
        backgroundColor: CURSOR_COLOR,
        opacity: isVisible ? 1 : 0,
      }}
    />
  );
};

export default BlinkingCursor;
