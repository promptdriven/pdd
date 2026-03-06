import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { AnimatedWord } from "./AnimatedWord";

import {
  TEXT_MAX_WIDTH,
  TEXT_PADDING_V,
  TEXT_PADDING_H,
  WINDOW_SIZE,
  SILENCE_GAP_FRAMES,
  SEGMENT_CLEAR_DURATION,
  BACKDROP_Y_START,
  BACKDROP_HEIGHT,
  RECENT_WINDOW_FRAMES,
  SUBTITLE_START_FRAME,
  WINDOW_SLIDE_DURATION,
} from "./constants";
import type { WordEntry } from "./constants";

interface WordByWordSubtitleProps {
  words: WordEntry[];
}

export const WordByWordSubtitle: React.FC<WordByWordSubtitleProps> = ({
  words,
}) => {
  const frame = useCurrentFrame();
  // The Sequence starts at SUBTITLE_START_FRAME, so local frame = frame.
  // Word startFrames are absolute, so convert to absolute for matching.
  const absoluteFrame = frame + SUBTITLE_START_FRAME;

  // Find words that have appeared so far
  const appearedWords = words.filter((w) => w.startFrame <= absoluteFrame);

  if (appearedWords.length === 0) return null;

  // Current active word is the last one that has started
  const lastAppeared = appearedWords[appearedWords.length - 1];
  const currentSegment = lastAppeared.segment;

  // Check if we're in a silence gap between segments
  const nextWord = words.find((w) => w.startFrame > absoluteFrame);
  const isInGap =
    nextWord &&
    nextWord.segment !== currentSegment &&
    absoluteFrame >= lastAppeared.endFrame + SILENCE_GAP_FRAMES;

  // Segment transition fade
  let segmentClearOpacity = 1;
  if (isInGap) {
    const gapStart = lastAppeared.endFrame + SILENCE_GAP_FRAMES;
    segmentClearOpacity = interpolate(
      absoluteFrame,
      [gapStart, gapStart + SEGMENT_CLEAR_DURATION],
      [1, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
  }

  // Determine rolling window
  const windowStart = Math.max(0, appearedWords.length - WINDOW_SIZE);
  const visibleWords = appearedWords.slice(windowStart);

  // Words being pushed out of the window
  const exitingWords =
    windowStart > 0
      ? appearedWords.slice(Math.max(0, windowStart - 1), windowStart)
      : [];

  // Smooth lateral scroll offset (easeInOutQuad) when window shifts
  let scrollOffset = 0;
  if (visibleWords.length > 0 && windowStart > 0) {
    const latestWordStart =
      visibleWords[visibleWords.length - 1].startFrame - SUBTITLE_START_FRAME;
    const slideProgress = interpolate(
      frame,
      [latestWordStart, latestWordStart + WINDOW_SLIDE_DURATION],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    const easedSlide = Easing.inOut(Easing.quad)(slideProgress);
    scrollOffset = interpolate(easedSlide, [0, 1], [-8, 0]);
  }

  // Determine word state for each visible word
  const getWordState = (
    w: WordEntry,
    globalIndex: number
  ): "current" | "recent" | "older" => {
    const activeIndex = appearedWords.length - 1;

    if (globalIndex === activeIndex) return "current";

    // "Recent" = word ended within last RECENT_WINDOW_FRAMES (0.5s)
    if (absoluteFrame - w.endFrame <= RECENT_WINDOW_FRAMES) return "recent";

    return "older";
  };

  return (
    <div
      style={{
        position: "absolute",
        top: BACKDROP_Y_START,
        left: 0,
        width: "100%",
        height: BACKDROP_HEIGHT,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        opacity: segmentClearOpacity,
        pointerEvents: "none",
      }}
    >
      <div
        style={{
          maxWidth: TEXT_MAX_WIDTH,
          padding: `${TEXT_PADDING_V}px ${TEXT_PADDING_H}px`,
          display: "flex",
          flexWrap: "wrap",
          alignItems: "center",
          justifyContent: "center",
          transform: `translateX(${scrollOffset}px)`,
          willChange: "transform",
        }}
      >
        {/* Exiting words (scrolled out of window) */}
        {exitingWords.map((w) => (
          <AnimatedWord
            key={`exit-${w.word}-${w.startFrame}`}
            word={w.word}
            wordStartFrame={w.startFrame - SUBTITLE_START_FRAME}
            wordEndFrame={w.endFrame - SUBTITLE_START_FRAME}
            state="exiting"
            exitStartFrame={
              visibleWords.length > 0
                ? visibleWords[0].startFrame - SUBTITLE_START_FRAME
                : frame
            }
          />
        ))}

        {/* Visible words in the rolling window */}
        {visibleWords.map((w, i) => {
          const globalIndex = windowStart + i;
          const wordState = getWordState(w, globalIndex);

          return (
            <AnimatedWord
              key={`word-${w.word}-${w.startFrame}`}
              word={w.word}
              wordStartFrame={w.startFrame - SUBTITLE_START_FRAME}
              wordEndFrame={w.endFrame - SUBTITLE_START_FRAME}
              state={wordState}
              exitStartFrame={0}
            />
          );
        })}
      </div>
    </div>
  );
};

export default WordByWordSubtitle;
