import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

import {
  FONT_FAMILY,
  FONT_SIZE,
  LETTER_SPACING,
  TEXT_SHADOW,
  HIGHLIGHT_SCALE_UP_FRAMES,
  HIGHLIGHT_SCALE_DOWN_FRAMES,
  CURRENT_COLOR,
  CURRENT_SCALE,
  CURRENT_WEIGHT,
  RECENT_COLOR,
  RECENT_OPACITY,
  RECENT_WEIGHT,
  OLDER_COLOR,
  OLDER_OPACITY,
  OLDER_WEIGHT,
  WORD_SPACING,
  WORD_FADE_DURATION,
  EXIT_DURATION,
  EXIT_SLIDE_PX,
  RECENT_WINDOW_FRAMES,
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

  // --- Determine base color, opacity, and weight by state ---
  let color: string;
  let targetOpacity: number;
  let fontWeight: number;

  switch (state) {
    case "current":
      color = CURRENT_COLOR;
      targetOpacity = 1.0;
      fontWeight = CURRENT_WEIGHT;
      break;
    case "recent":
      color = RECENT_COLOR;
      targetOpacity = RECENT_OPACITY;
      fontWeight = RECENT_WEIGHT;
      break;
    case "older":
      color = OLDER_COLOR;
      targetOpacity = OLDER_OPACITY;
      fontWeight = OLDER_WEIGHT;
      break;
    case "exiting":
      color = OLDER_COLOR;
      targetOpacity = OLDER_OPACITY;
      fontWeight = OLDER_WEIGHT;
      break;
  }

  // --- Word appear: opacity 0→1 over 6 frames (easeOutQuad) ---
  const appearProgress = interpolate(
    frame,
    [wordStartFrame, wordStartFrame + 6],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const appearOpacity = Easing.out(Easing.quad)(appearProgress);

  // --- Highlight scale pulse for current word ---
  let highlightScale = 1.0;
  if (state === "current") {
    const scaleUpProgress = interpolate(
      frame,
      [wordStartFrame, wordStartFrame + HIGHLIGHT_SCALE_UP_FRAMES],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    const scaleDownProgress = interpolate(
      frame,
      [
        wordStartFrame + HIGHLIGHT_SCALE_UP_FRAMES,
        wordStartFrame + HIGHLIGHT_SCALE_UP_FRAMES + HIGHLIGHT_SCALE_DOWN_FRAMES,
      ],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );

    if (scaleDownProgress > 0) {
      const easedDown = Easing.in(Easing.cubic)(scaleDownProgress);
      highlightScale = interpolate(easedDown, [0, 1], [CURRENT_SCALE, 1.0]);
    } else {
      const easedUp = Easing.out(Easing.cubic)(scaleUpProgress);
      highlightScale = interpolate(easedUp, [0, 1], [1.0, CURRENT_SCALE]);
    }
  }

  // --- Recent/older word fade: smooth transition after word ends ---
  let fadedOpacity = targetOpacity;
  if ((state === "recent" || state === "older") && wordEndFrame > 0) {
    const fadeProgress = interpolate(
      frame,
      [wordEndFrame, wordEndFrame + WORD_FADE_DURATION],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    const easedFade = Easing.out(Easing.quad)(fadeProgress);
    fadedOpacity = interpolate(easedFade, [0, 1], [1.0, targetOpacity]);
  }

  // --- Exit animation: slide left + fade out over EXIT_DURATION ---
  let exitOpacity = 1;
  let exitTranslateX = 0;
  if (state === "exiting" && exitStartFrame > 0) {
    const exitProgress = interpolate(
      frame,
      [exitStartFrame, exitStartFrame + EXIT_DURATION],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    const easedExit = Easing.inOut(Easing.cubic)(exitProgress);
    exitOpacity = interpolate(easedExit, [0, 1], [OLDER_OPACITY, 0]);
    exitTranslateX = interpolate(easedExit, [0, 1], [0, -EXIT_SLIDE_PX]);
  }

  // --- Combine final values ---
  const finalScale = state === "current" ? highlightScale : 1.0;
  const baseOpacity =
    state === "recent" || state === "older" ? fadedOpacity : targetOpacity;
  const finalOpacity = baseOpacity * exitOpacity * appearOpacity;

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
        position: "relative",
      }}
    >
      {word}
    </span>
  );
};

export default AnimatedWord;
