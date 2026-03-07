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
  PREVIOUS_COLOR,
  PREVIOUS_OPACITY,
  UPCOMING_COLOR,
  UPCOMING_OPACITY,
  WORD_SPACING,
  UNDERLINE_COLOR,
  UNDERLINE_OPACITY,
  UNDERLINE_HEIGHT,
  WORD_FADE_DURATION,
  EXIT_DURATION,
  EXIT_SLIDE_PX,
} from "./constants";

export type WordState = "current" | "previous" | "upcoming" | "exiting";

interface AnimatedWordProps {
  word: string;
  /** Frame (within the Sequence) when this word starts being spoken */
  wordStartFrame: number;
  /** Frame (within the Sequence) when this word stops being spoken */
  wordEndFrame: number;
  state: WordState;
  /** Frame (within the Sequence) when exit animation begins (for "exiting" state) */
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

  // --- Determine base color and opacity by state ---
  let color: string;
  let targetOpacity: number;

  switch (state) {
    case "current":
      color = CURRENT_COLOR;
      targetOpacity = 1.0;
      break;
    case "previous":
      color = PREVIOUS_COLOR;
      targetOpacity = PREVIOUS_OPACITY;
      break;
    case "upcoming":
      color = UPCOMING_COLOR;
      targetOpacity = UPCOMING_OPACITY;
      break;
    case "exiting":
      color = PREVIOUS_COLOR;
      targetOpacity = PREVIOUS_OPACITY;
      break;
  }

  // --- Highlight scale pulse for current word ---
  // Scale 1.0→1.05 over 3 frames (easeOutQuad), then 1.05→1.0 over 6 frames (easeOutQuad)
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
      const easedDown = Easing.out(Easing.quad)(scaleDownProgress);
      highlightScale = interpolate(easedDown, [0, 1], [CURRENT_SCALE, 1.0]);
    } else {
      const easedUp = Easing.out(Easing.quad)(scaleUpProgress);
      highlightScale = interpolate(easedUp, [0, 1], [1.0, CURRENT_SCALE]);
    }
  }

  // --- Previous word fade: opacity 1.0→0.5 over WORD_FADE_DURATION after word ends ---
  let fadedOpacity = targetOpacity;
  if (state === "previous" && wordEndFrame > 0) {
    const fadeProgress = interpolate(
      frame,
      [wordEndFrame, wordEndFrame + WORD_FADE_DURATION],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    const easedFade = Easing.out(Easing.quad)(fadeProgress);
    fadedOpacity = interpolate(easedFade, [0, 1], [1.0, PREVIOUS_OPACITY]);
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
    exitOpacity = interpolate(easedExit, [0, 1], [PREVIOUS_OPACITY, 0]);
    exitTranslateX = interpolate(easedExit, [0, 1], [0, -EXIT_SLIDE_PX]);
  }

  // --- Combine final values ---
  const finalScale = state === "current" ? highlightScale : 1.0;
  const baseOpacity = state === "previous" ? fadedOpacity : targetOpacity;
  const finalOpacity = baseOpacity * exitOpacity;

  // Amber underline only on current word
  const showUnderline = state === "current";

  return (
    <span
      style={{
        display: "inline-block",
        fontFamily: FONT_FAMILY,
        fontSize: FONT_SIZE,
        fontWeight: 600,
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
      {showUnderline && (
        <span
          style={{
            position: "absolute",
            bottom: -2,
            left: 0,
            width: "100%",
            height: UNDERLINE_HEIGHT,
            backgroundColor: UNDERLINE_COLOR,
            opacity: UNDERLINE_OPACITY,
            borderRadius: 1,
          }}
        />
      )}
    </span>
  );
};

export default AnimatedWord;
