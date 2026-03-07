import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

import {
  FONT_FAMILY,
  FONT_SIZE,
  TEXT_SHADOW,
  HIGHLIGHT_SCALE_UP_FRAMES,
  HIGHLIGHT_SCALE_DOWN_FRAMES,
  WORD_FADE_DURATION,
  EXIT_DURATION,
  EXIT_SLIDE_PX,
  P2_CURRENT_COLOR,
  P2_CURRENT_SCALE,
  P2_CURRENT_WEIGHT,
  P2_RECENT_COLOR,
  P2_RECENT_OPACITY,
  P2_RECENT_WEIGHT,
  P2_OLDER_COLOR,
  P2_OLDER_OPACITY,
  P2_OLDER_WEIGHT,
  P2_UNDERLINE_COLOR,
  UNDERLINE_OPACITY,
  UNDERLINE_HEIGHT,
  P2_LETTER_SPACING,
  P2_WORD_SPACING,
} from "./constants";

export type Part2WordState = "current" | "previous" | "upcoming" | "exiting";

interface Part2AnimatedWordProps {
  word: string;
  wordStartFrame: number;
  wordEndFrame: number;
  state: Part2WordState;
  exitStartFrame: number;
  isRecent: boolean;
}

export const Part2AnimatedWord: React.FC<Part2AnimatedWordProps> = ({
  word,
  wordStartFrame,
  wordEndFrame,
  state,
  exitStartFrame,
  isRecent,
}) => {
  const frame = useCurrentFrame();

  // --- Determine base color, opacity, and weight by state ---
  let color: string;
  let targetOpacity: number;
  let fontWeight: number;

  switch (state) {
    case "current":
      color = P2_CURRENT_COLOR;
      targetOpacity = 1.0;
      fontWeight = P2_CURRENT_WEIGHT;
      break;
    case "previous":
      if (isRecent) {
        color = P2_RECENT_COLOR;
        targetOpacity = P2_RECENT_OPACITY;
        fontWeight = P2_RECENT_WEIGHT;
      } else {
        color = P2_OLDER_COLOR;
        targetOpacity = P2_OLDER_OPACITY;
        fontWeight = P2_OLDER_WEIGHT;
      }
      break;
    case "upcoming":
      color = P2_OLDER_COLOR;
      targetOpacity = P2_OLDER_OPACITY;
      fontWeight = P2_OLDER_WEIGHT;
      break;
    case "exiting":
      color = P2_OLDER_COLOR;
      targetOpacity = P2_OLDER_OPACITY;
      fontWeight = P2_OLDER_WEIGHT;
      break;
  }

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
      highlightScale = interpolate(easedDown, [0, 1], [P2_CURRENT_SCALE, 1.0]);
    } else {
      const easedUp = Easing.out(Easing.cubic)(scaleUpProgress);
      highlightScale = interpolate(easedUp, [0, 1], [1.0, P2_CURRENT_SCALE]);
    }
  }

  // --- Word appear: opacity 0→1 over 6 frames (easeOutQuad) ---
  const appearProgress = interpolate(
    frame,
    [wordStartFrame, wordStartFrame + WORD_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const appearOpacity = Easing.out(Easing.quad)(appearProgress);

  // --- Previous word fade after word ends ---
  let fadedOpacity = targetOpacity;
  if (state === "previous" && wordEndFrame > 0) {
    const fadeProgress = interpolate(
      frame,
      [wordEndFrame, wordEndFrame + WORD_FADE_DURATION],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    const easedFade = Easing.out(Easing.quad)(fadeProgress);
    fadedOpacity = interpolate(easedFade, [0, 1], [1.0, targetOpacity]);
  }

  // --- Exit animation: slide left + fade out ---
  let exitOpacity = 1;
  let exitTranslateX = 0;
  if (state === "exiting" && exitStartFrame > 0) {
    const exitProgress = interpolate(
      frame,
      [exitStartFrame, exitStartFrame + EXIT_DURATION],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    const easedExit = Easing.inOut(Easing.quad)(exitProgress);
    exitOpacity = interpolate(easedExit, [0, 1], [P2_OLDER_OPACITY, 0]);
    exitTranslateX = interpolate(easedExit, [0, 1], [0, -EXIT_SLIDE_PX]);
  }

  // --- Combine final values ---
  const finalScale = state === "current" ? highlightScale : 1.0;
  const baseOpacity = state === "previous" ? fadedOpacity : targetOpacity;
  const finalOpacity = baseOpacity * exitOpacity * appearOpacity;

  const showUnderline = state === "current";

  return (
    <span
      style={{
        display: "inline-block",
        fontFamily: FONT_FAMILY,
        fontSize: FONT_SIZE,
        fontWeight,
        letterSpacing: P2_LETTER_SPACING,
        color,
        textShadow: TEXT_SHADOW,
        transform: `scale(${finalScale}) translateX(${exitTranslateX}px)`,
        opacity: finalOpacity,
        marginRight: P2_WORD_SPACING,
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
            backgroundColor: P2_UNDERLINE_COLOR,
            opacity: UNDERLINE_OPACITY,
            borderRadius: 1,
          }}
        />
      )}
    </span>
  );
};

export default Part2AnimatedWord;
