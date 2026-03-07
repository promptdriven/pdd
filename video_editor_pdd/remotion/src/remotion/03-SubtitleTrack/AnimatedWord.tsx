import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

import {
  FONT_FAMILY,
  FONT_SIZE,
  TEXT_SHADOW,
  WORD_SPACING,
  POP_IN_DURATION,
  POP_IN_SCALE_START,
  POP_IN_SCALE_END,
  DIM_DURATION,
  EXIT_DURATION,
  EXIT_SLIDE_PX,
  ACTIVE_COLOR,
  ACTIVE_WEIGHT,
  ACTIVE_SCALE,
  TRAIL_COLOR,
  TRAIL_WEIGHT,
} from "./constants";

// Custom easeOutBack for word pop-in (slight overshoot for punch)
const easeOutBack = (t: number): number => {
  const c1 = 1.70158;
  const c3 = c1 + 1;
  return 1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2);
};

interface AnimatedWordProps {
  word: string;
  wordStartFrame: number;
  isActive: boolean;
  isExiting: boolean;
  exitStartFrame: number;
}

export const AnimatedWord: React.FC<AnimatedWordProps> = ({
  word,
  wordStartFrame,
  isActive,
  isExiting,
  exitStartFrame,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - wordStartFrame;

  // Word hasn't appeared yet
  if (localFrame < 0) return null;

  // --- Pop-in animation: scale 0.85→1.0, opacity 0→1 (easeOutBack) ---
  const popInProgress = Math.min(localFrame / POP_IN_DURATION, 1);
  const easedPopIn = easeOutBack(popInProgress);

  const popInScale = interpolate(
    easedPopIn,
    [0, 1],
    [POP_IN_SCALE_START, POP_IN_SCALE_END]
  );
  const popInOpacity = interpolate(
    localFrame,
    [0, POP_IN_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // --- Active vs trailing state ---
  let targetScale: number;
  let targetOpacity: number;
  let fontWeight: number;
  let color: string;

  if (isActive) {
    targetScale = ACTIVE_SCALE;
    targetOpacity = 1;
    fontWeight = ACTIVE_WEIGHT;
    color = ACTIVE_COLOR;
  } else {
    // Dim transition: easeOutQuad over DIM_DURATION frames after pop-in completes
    const dimFrame = frame - (wordStartFrame + POP_IN_DURATION);
    const dimProgress = Math.min(Math.max(dimFrame / DIM_DURATION, 0), 1);
    const easedDim = Easing.out(Easing.quad)(dimProgress);

    targetScale = interpolate(easedDim, [0, 1], [ACTIVE_SCALE, 1.0]);
    targetOpacity = interpolate(easedDim, [0, 1], [1, 0.6]);
    fontWeight = TRAIL_WEIGHT;
    color = TRAIL_COLOR;
  }

  // --- Window overflow exit animation (easeInOutCubic) ---
  let exitOpacity = 1;
  let exitTranslateX = 0;

  if (isExiting) {
    const exitLocalFrame = frame - exitStartFrame;
    const exitProgress = Math.min(Math.max(exitLocalFrame / EXIT_DURATION, 0), 1);
    const easedExit = Easing.inOut(Easing.cubic)(exitProgress);

    exitOpacity = interpolate(easedExit, [0, 1], [1, 0]);
    exitTranslateX = interpolate(easedExit, [0, 1], [0, -EXIT_SLIDE_PX]);
  }

  // --- Combine animations ---
  const isStillAppearing = localFrame < POP_IN_DURATION;
  const finalScale = isStillAppearing ? popInScale : targetScale;
  const finalOpacity =
    (isStillAppearing ? popInOpacity : targetOpacity) * exitOpacity;

  return (
    <span
      style={{
        display: "inline-block",
        fontFamily: FONT_FAMILY,
        fontSize: FONT_SIZE,
        fontWeight,
        color,
        textShadow: TEXT_SHADOW,
        transform: `scale(${finalScale}) translateX(${exitTranslateX}px)`,
        opacity: finalOpacity,
        marginRight: WORD_SPACING,
        whiteSpace: "nowrap",
        willChange: "transform, opacity",
      }}
    >
      {word}
    </span>
  );
};

export default AnimatedWord;
