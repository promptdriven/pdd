import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { AnimatedWord } from "./AnimatedWord";

import {
  TEXT_MAX_WIDTH,
  TEXT_PADDING_V,
  TEXT_PADDING_H,
  BACKDROP_HEIGHT,
  WINDOW_SIZE,
  SILENCE_GAP_FRAMES,
  SEGMENT_CLEAR_DURATION,
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

  // Find words that have appeared so far
  const appearedWords = words.filter((w) => w.startFrame <= frame);

  if (appearedWords.length === 0) return null;

  // Current active word is the last one that started
  const lastAppeared = appearedWords[appearedWords.length - 1];
  const currentSegment = lastAppeared.segment;

  // Check if we're in a silence gap between segments
  const nextWord = words.find((w) => w.startFrame > frame);
  const isInGap =
    nextWord &&
    nextWord.segment !== currentSegment &&
    frame >= lastAppeared.startFrame + SILENCE_GAP_FRAMES;

  // Segment clear fade (10-frame fade when in gap)
  let segmentClearOpacity = 1;
  if (isInGap) {
    const gapStart = lastAppeared.startFrame + SILENCE_GAP_FRAMES;
    segmentClearOpacity = interpolate(
      frame,
      [gapStart, gapStart + SEGMENT_CLEAR_DURATION],
      [1, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
  }

  // Determine rolling window (max 12 words visible)
  const windowStart = Math.max(0, appearedWords.length - WINDOW_SIZE);
  const visibleWords = appearedWords.slice(windowStart);

  // Words being pushed out of the window
  const exitingWords =
    windowStart > 0
      ? appearedWords.slice(Math.max(0, windowStart - 1), windowStart)
      : [];

  // Smooth lateral scroll when window shifts (easeInOutCubic)
  let scrollOffset = 0;
  if (visibleWords.length > 0 && windowStart > 0) {
    const latestWordStart = visibleWords[visibleWords.length - 1].startFrame;
    const slideProgress = interpolate(
      frame,
      [latestWordStart, latestWordStart + WINDOW_SLIDE_DURATION],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    const easedSlide = Easing.inOut(Easing.cubic)(slideProgress);
    scrollOffset = interpolate(easedSlide, [0, 1], [-8, 0]);
  }

  // Active word index (last appeared word)
  const activeIndex = appearedWords.length - 1;

  return (
    <div
      style={{
        position: "absolute",
        bottom: 0,
        left: 0,
        width: 1920,
        height: BACKDROP_HEIGHT,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        opacity: segmentClearOpacity,
        overflow: "hidden",
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
            wordStartFrame={w.startFrame}
            isActive={false}
            isExiting={true}
            exitStartFrame={
              visibleWords.length > 0 ? visibleWords[0].startFrame : frame
            }
          />
        ))}

        {/* Visible words in the rolling window */}
        {visibleWords.map((w, i) => {
          const globalIndex = windowStart + i;
          return (
            <AnimatedWord
              key={`word-${w.word}-${w.startFrame}`}
              word={w.word}
              wordStartFrame={w.startFrame}
              isActive={globalIndex === activeIndex}
              isExiting={false}
              exitStartFrame={0}
            />
          );
        })}
      </div>
    </div>
  );
};

export default WordByWordSubtitle;
