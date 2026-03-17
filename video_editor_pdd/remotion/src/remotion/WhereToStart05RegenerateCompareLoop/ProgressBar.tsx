import React from "react";
import { interpolate, Easing } from "remotion";
import {
  PROGRESS_Y,
  PROGRESS_WIDTH,
  PROGRESS_HEIGHT,
  TRACK_COLOR,
  BLUE,
  GREEN,
  WIDTH,
  STEP1_START,
  STEP2_START,
  STEP3_START,
  STEP4_START,
  LOOP_START,
} from "./constants";

// Keyframes: [frame, value]
const KEYFRAMES: [number, number][] = [
  [STEP1_START, 0],
  [STEP2_START, 0.25],
  [STEP3_START, 0.5],
  [STEP4_START, 0.75],
  [LOOP_START, 1.0],
  [155, 0.8],
];

export const ProgressBar: React.FC<{ frame: number }> = ({ frame }) => {
  // Compute fill fraction from keyframes
  let fillFraction = 0;
  for (let i = 0; i < KEYFRAMES.length - 1; i++) {
    const [startFrame, startVal] = KEYFRAMES[i];
    const [endFrame, endVal] = KEYFRAMES[i + 1];
    if (frame >= startFrame && frame <= endFrame) {
      fillFraction = interpolate(frame, [startFrame, endFrame], [startVal, endVal], {
        easing: Easing.out(Easing.quad),
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      });
      break;
    } else if (frame > endFrame) {
      fillFraction = endVal;
    }
  }

  // After the last keyframe, hold at that value
  if (frame >= KEYFRAMES[KEYFRAMES.length - 1][0]) {
    fillFraction = KEYFRAMES[KEYFRAMES.length - 1][1];
  }

  const barLeft = (WIDTH - PROGRESS_WIDTH) / 2;

  return (
    <div
      style={{
        position: "absolute",
        left: barLeft,
        top: PROGRESS_Y,
        width: PROGRESS_WIDTH,
        height: PROGRESS_HEIGHT,
        backgroundColor: TRACK_COLOR,
        borderRadius: 3,
        overflow: "hidden",
      }}
    >
      <div
        style={{
          width: `${fillFraction * 100}%`,
          height: "100%",
          background: `linear-gradient(to right, ${BLUE}, ${GREEN})`,
          borderRadius: 3,
          transition: "none",
        }}
      />
    </div>
  );
};
