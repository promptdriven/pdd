import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import { Part2AnimatedWord } from "./Part2AnimatedWord";
import type { Part2WordState } from "./Part2AnimatedWord";

import {
  TEXT_MAX_WIDTH,
  TEXT_PADDING_V,
  TEXT_PADDING_H,
  WINDOW_SIZE,
  SILENCE_GAP_FRAMES,
  SEGMENT_CLEAR_DURATION,
  P2_BACKDROP_Y_START,
  P2_BACKDROP_HEIGHT,
  P2_RECENT_THRESHOLD_FRAMES,
} from "./constants";
import type { WordEntry } from "./constants";

interface Part2WordByWordSubtitleProps {
  words: WordEntry[];
}

export const Part2WordByWordSubtitle: React.FC<Part2WordByWordSubtitleProps> = ({
  words,
}) => {
  const frame = useCurrentFrame();

  // Find all words that have started by the current frame
  const appearedWords = words.filter((w) => w.startFrame <= frame);

  if (appearedWords.length === 0) return null;

  // The most recently started word is "current"
  const lastAppeared = appearedWords[appearedWords.length - 1];
  const currentSegment = lastAppeared.segment;

  // Check for silence gap between segments — fade out old segment
  const nextWord = words.find((w) => w.startFrame > frame);
  const isInGap =
    nextWord &&
    nextWord.segment !== currentSegment &&
    frame >= lastAppeared.endFrame + SILENCE_GAP_FRAMES;

  let segmentClearOpacity = 1;
  if (isInGap) {
    const gapStart = lastAppeared.endFrame + SILENCE_GAP_FRAMES;
    segmentClearOpacity = interpolate(
      frame,
      [gapStart, gapStart + SEGMENT_CLEAR_DURATION],
      [1, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
  }

  // Rolling window: show last WINDOW_SIZE words
  const windowStart = Math.max(0, appearedWords.length - WINDOW_SIZE);
  const visibleWords = appearedWords.slice(windowStart);

  // Words being pushed out of the window (exit animation)
  const exitingWords =
    windowStart > 0
      ? appearedWords.slice(Math.max(0, windowStart - 1), windowStart)
      : [];

  // Determine word state
  const getWordState = (globalIndex: number): Part2WordState => {
    const activeIndex = appearedWords.length - 1;
    if (globalIndex === activeIndex) return "current";
    if (globalIndex < activeIndex) return "previous";
    return "upcoming";
  };

  // Determine if a word is "recent" (spoken within last 0.5s = 15 frames)
  const isRecent = (w: WordEntry): boolean => {
    return frame - w.endFrame < P2_RECENT_THRESHOLD_FRAMES && frame >= w.endFrame;
  };

  return (
    <div
      style={{
        position: "absolute",
        top: P2_BACKDROP_Y_START,
        left: 0,
        width: "100%",
        height: P2_BACKDROP_HEIGHT,
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
          flexWrap: "nowrap",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        {/* Exiting words (scrolled out of window) */}
        {exitingWords.map((w) => (
          <Part2AnimatedWord
            key={`exit-${w.word}-${w.startFrame}`}
            word={w.word}
            wordStartFrame={w.startFrame}
            wordEndFrame={w.endFrame}
            state="exiting"
            exitStartFrame={
              visibleWords.length > 0 ? visibleWords[0].startFrame : frame
            }
            isRecent={false}
          />
        ))}

        {/* Visible words in the rolling window */}
        {visibleWords.map((w, i) => {
          const globalIndex = windowStart + i;
          const wordState = getWordState(globalIndex);

          return (
            <Part2AnimatedWord
              key={`word-${w.word}-${w.startFrame}`}
              word={w.word}
              wordStartFrame={w.startFrame}
              wordEndFrame={w.endFrame}
              state={wordState}
              exitStartFrame={0}
              isRecent={wordState === "previous" && isRecent(w)}
            />
          );
        })}
      </div>
    </div>
  );
};

export default Part2WordByWordSubtitle;
