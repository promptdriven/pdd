import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  REALIZATION_FLASH_START,
  REALIZATION_FLASH_RAMP_UP,
  REALIZATION_FLASH_RAMP_DOWN,
  FLASH_COLOR,
  FLASH_PEAK_OPACITY,
} from "./constants";

export const RealizationFlash: React.FC = () => {
  const frame = useCurrentFrame();

  const totalDur = REALIZATION_FLASH_RAMP_UP + REALIZATION_FLASH_RAMP_DOWN;
  const flashOpacity = interpolate(
    frame,
    [
      REALIZATION_FLASH_START,
      REALIZATION_FLASH_START + REALIZATION_FLASH_RAMP_UP,
      REALIZATION_FLASH_START + totalDur,
    ],
    [0, FLASH_PEAK_OPACITY, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  if (flashOpacity <= 0) return null;

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        backgroundColor: FLASH_COLOR,
        opacity: flashOpacity,
        pointerEvents: "none",
      }}
    />
  );
};

export default RealizationFlash;
