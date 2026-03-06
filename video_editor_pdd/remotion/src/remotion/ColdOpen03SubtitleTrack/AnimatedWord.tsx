import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

const FONT_FAMILY = "'Inter', sans-serif";
const FONT_SIZE = 36;
const TEXT_SHADOW = "0 2px 8px rgba(0, 0, 0, 0.5)";
const POP_IN_DURATION = 4;
const DIM_DURATION = 3;

// Custom easeOutBack for word pop-in (slight overshoot)
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

  // Pop-in animation: scale 0.85→1.0, opacity 0→1 over POP_IN_DURATION frames
  const popInProgress = Math.min(localFrame / POP_IN_DURATION, 1);
  const easedPopIn = easeOutBack(popInProgress);

  const popInScale = interpolate(easedPopIn, [0, 1], [0.85, 1.0]);
  const popInOpacity = interpolate(
    localFrame,
    [0, POP_IN_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Active vs trailing state
  let targetScale: number;
  let targetOpacity: number;
  let fontWeight: number;

  if (isActive) {
    targetScale = 1.05;
    targetOpacity = 1;
    fontWeight = 600;
  } else {
    // Dim transition after losing active state
    const dimFrame = frame - (wordStartFrame + POP_IN_DURATION);
    const dimProgress = Math.min(Math.max(dimFrame / DIM_DURATION, 0), 1);
    const easedDim = Easing.out(Easing.quad)(dimProgress);

    targetScale = interpolate(easedDim, [0, 1], [1.05, 1.0]);
    targetOpacity = interpolate(easedDim, [0, 1], [1, 0.6]);
    fontWeight = 500;
  }

  // Window overflow exit animation
  let exitOpacity = 1;
  let exitTranslateX = 0;

  if (isExiting) {
    const exitLocalFrame = frame - exitStartFrame;
    const exitProgress = Math.min(Math.max(exitLocalFrame / 6, 0), 1);
    const easedExit = Easing.inOut(Easing.cubic)(exitProgress);

    exitOpacity = interpolate(easedExit, [0, 1], [1, 0]);
    exitTranslateX = interpolate(easedExit, [0, 1], [0, -20]);
  }

  // Combine animations
  const finalScale = localFrame < POP_IN_DURATION ? popInScale : targetScale;
  const finalOpacity =
    (localFrame < POP_IN_DURATION ? popInOpacity : targetOpacity) * exitOpacity;

  return (
    <span
      style={{
        display: "inline-block",
        fontFamily: FONT_FAMILY,
        fontSize: FONT_SIZE,
        fontWeight,
        color: isActive ? "#FFFFFF" : "rgba(255, 255, 255, 0.6)",
        textShadow: TEXT_SHADOW,
        transform: `scale(${finalScale}) translateX(${exitTranslateX}px)`,
        opacity: finalOpacity,
        marginRight: 12,
        whiteSpace: "nowrap",
        willChange: "transform, opacity",
      }}
    >
      {word}
    </span>
  );
};

export default AnimatedWord;
