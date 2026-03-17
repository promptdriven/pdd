import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  UI_FONT,
  EQUIV_SIZE,
  TEXT_COLOR,
  EQUIV_FADE_START,
  EQUIV_FADE_DURATION,
  EQUIV_PULSE_PERIOD,
  EQUIV_MIN_OPACITY,
  EQUIV_MAX_OPACITY,
  CENTER_Y,
  CANVAS_WIDTH,
} from "./constants";

export const EquivalenceSymbol: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [EQUIV_FADE_START, EQUIV_FADE_START + EQUIV_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  if (frame < EQUIV_FADE_START) return null;

  // Pulse opacity between min and max on a sine cycle
  const pulsePhase = (frame - EQUIV_FADE_START - EQUIV_FADE_DURATION) / EQUIV_PULSE_PERIOD;
  const pulseT = frame > EQUIV_FADE_START + EQUIV_FADE_DURATION
    ? (Math.sin(pulsePhase * Math.PI * 2) + 1) / 2
    : 1;
  const pulseOpacity = EQUIV_MIN_OPACITY + (EQUIV_MAX_OPACITY - EQUIV_MIN_OPACITY) * pulseT;

  const opacity = fadeIn * pulseOpacity;

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: CENTER_Y - EQUIV_SIZE / 2 - 10,
        width: CANVAS_WIDTH,
        textAlign: "center",
        fontFamily: UI_FONT,
        fontSize: EQUIV_SIZE,
        fontWeight: 700,
        color: TEXT_COLOR,
        opacity,
        filter: `drop-shadow(0 0 20px rgba(226, 232, 240, 0.08))`,
        pointerEvents: "none",
      }}
    >
      ≡
    </div>
  );
};

export default EquivalenceSymbol;
