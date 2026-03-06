import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

import {
  FONT_FAMILY,
  FONT_SIZE,
  LETTER_SPACING,
  TEXT_SHADOW,
  WORD_APPEAR_DURATION,
  HIGHLIGHT_SCALE_UP_FRAMES,
  HIGHLIGHT_SCALE_DOWN_FRAMES,
  EXIT_DURATION,
  EXIT_SLIDE_PX,
  CURRENT_COLOR,
  CURRENT_WEIGHT,
  CURRENT_SCALE,
  PREVIOUS_COLOR,
  PREVIOUS_OPACITY,
  PREVIOUS_WEIGHT,
  UPCOMING_COLOR,
  UPCOMING_OPACITY,
  UPCOMING_WEIGHT,
  WORD_SPACING,
  UNDERLINE_COLOR,
  UNDERLINE_OPACITY,
  UNDERLINE_HEIGHT,
  WORD_FADE_DURATION,
} from "./constants";

type WordState = "current" | "previous" | "upcoming" | "exiting";

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

  // --- Determine color/weight/opacity based on state ---
  let color: string;
  let fontWeight: number;
  let targetOpacity: number;

  switch (state) {
    case "current":
      color = CURRENT_COLOR;
      fontWeight = CURRENT_WEIGHT;
      targetOpacity = 1;
      break;
    case "previous":
      color = PREVIOUS_COLOR;
      fontWeight = PREVIOUS_WEIGHT;
      targetOpacity = PREVIOUS_OPACITY;
      break;
    case "upcoming":
      color = UPCOMING_COLOR;
      fontWeight = UPCOMING_WEIGHT;
      targetOpacity = UPCOMING_OPACITY;
      break;
    case "exiting":
      color = PREVIOUS_COLOR;
      fontWeight = PREVIOUS_WEIGHT;
      targetOpacity = PREVIOUS_OPACITY;
      break;
  }

  // --- Highlight scale pulse: 1.0→1.05 over 3 frames, 1.05→1.0 over 6 frames ---
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
      // Scaling back down
      const easedDown = Easing.out(Easing.quad)(scaleDownProgress);
      highlightScale = interpolate(easedDown, [0, 1], [CURRENT_SCALE, 1.0]);
    } else {
      // Scaling up
      const easedUp = Easing.out(Easing.quad)(scaleUpProgress);
      highlightScale = interpolate(easedUp, [0, 1], [1.0, CURRENT_SCALE]);
    }
  }

  // --- Previous word fade: opacity 1.0→0.5 over WORD_FADE_DURATION ---
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

  // --- Exit animation (sliding left, fading out over EXIT_DURATION) ---
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
    const easedExit = Easing.inOut(Easing.cubic)(exitProgress);

    exitOpacity = interpolate(easedExit, [0, 1], [0.5, 0]);
    exitTranslateX = interpolate(easedExit, [0, 1], [0, -EXIT_SLIDE_PX]);
  }

  // --- Combine animations ---
  const isStillAppearing = localFrame < WORD_APPEAR_DURATION;
  const finalScale = isStillAppearing
    ? popInScale
    : state === "current"
      ? highlightScale
      : 1.0;
  const baseOpacity =
    state === "previous" ? fadedOpacity : (isStillAppearing ? popInOpacity : targetOpacity);
  const finalOpacity = baseOpacity * exitOpacity;

  // Show amber underline only on current word
  const showUnderline = state === "current";

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
