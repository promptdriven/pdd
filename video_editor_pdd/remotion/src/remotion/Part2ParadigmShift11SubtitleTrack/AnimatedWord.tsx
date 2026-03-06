import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

import {
  FONT_FAMILY,
  FONT_SIZE,
  LETTER_SPACING,
  TEXT_SHADOW,
  WORD_APPEAR_DURATION,
  HIGHLIGHT_DURATION,
  EXIT_DURATION,
  EXIT_SLIDE_PX,
  CURRENT_COLOR,
  CURRENT_WEIGHT,
  CURRENT_SCALE,
  RECENT_COLOR,
  RECENT_WEIGHT,
  OLDER_COLOR,
  OLDER_OPACITY,
  OLDER_WEIGHT,
  WORD_SPACING,
} from "./constants";

export type WordState = "current" | "recent" | "older" | "exiting";

interface AnimatedWordProps {
  word: string;
  wordStartFrame: number;
  wordEndFrame: number;
  state: WordState;
  exitStartFrame: number;
}

export const AnimatedWord: React.FC<AnimatedWordProps> = ({
  word,
  wordStartFrame,
  wordEndFrame,
  state,
  exitStartFrame,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - wordStartFrame;

  // Word hasn't appeared yet
  if (localFrame < 0) return null;

  // --- Pop-in animation (easeOutQuad) ---
  const popInProgress = interpolate(
    localFrame,
    [0, WORD_APPEAR_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const easedPopIn = Easing.out(Easing.quad)(popInProgress);

  const popInOpacity = easedPopIn;
  const popInScale = interpolate(easedPopIn, [0, 1], [0.9, 1.0]);

  // --- Determine color/weight/scale based on state ---
  let color: string;
  let fontWeight: number;
  let targetScale: number;
  let targetOpacity: number;

  switch (state) {
    case "current":
      color = CURRENT_COLOR;
      fontWeight = CURRENT_WEIGHT;
      targetScale = CURRENT_SCALE;
      targetOpacity = 1;
      break;
    case "recent":
      color = RECENT_COLOR;
      fontWeight = RECENT_WEIGHT;
      targetScale = 1.0;
      targetOpacity = 0.9;
      break;
    case "older":
      color = OLDER_COLOR;
      fontWeight = OLDER_WEIGHT;
      targetScale = 1.0;
      targetOpacity = OLDER_OPACITY;
      break;
    case "exiting":
      color = OLDER_COLOR;
      fontWeight = OLDER_WEIGHT;
      targetScale = 1.0;
      targetOpacity = OLDER_OPACITY;
      break;
  }

  // --- Highlight scale pulse (easeOutCubic then easeInCubic) ---
  const isHighlighting = frame >= wordStartFrame && frame <= wordEndFrame;
  let highlightScale = 1.0;
  if (state === "current" && isHighlighting) {
    const highlightProgress = interpolate(
      frame,
      [wordStartFrame, wordStartFrame + HIGHLIGHT_DURATION],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    const easedHighlight = Easing.out(Easing.cubic)(highlightProgress);
    highlightScale = interpolate(easedHighlight, [0, 1], [1.0, CURRENT_SCALE]);
  }

  // --- Exit animation (sliding left, fading out) ---
  let exitOpacity = 1;
  let exitTranslateX = 0;

  if (state === "exiting" && exitStartFrame > 0) {
    const exitLocalFrame = frame - exitStartFrame;
    const exitProgress = interpolate(
      exitLocalFrame,
      [0, EXIT_DURATION],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    const easedExit = Easing.inOut(Easing.quad)(exitProgress);

    exitOpacity = interpolate(easedExit, [0, 1], [0.4, 0]);
    exitTranslateX = interpolate(easedExit, [0, 1], [0, -EXIT_SLIDE_PX]);
  }

  // --- Combine animations ---
  const isStillAppearing = localFrame < WORD_APPEAR_DURATION;
  const finalScale = isStillAppearing
    ? popInScale
    : state === "current"
      ? highlightScale
      : targetScale;
  const finalOpacity =
    (isStillAppearing ? popInOpacity : targetOpacity) * exitOpacity;

  return (
    <span
      style={{
        display: "inline-block",
        fontFamily: FONT_FAMILY,
        fontSize: FONT_SIZE,
        fontWeight,
        letterSpacing: LETTER_SPACING,
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
