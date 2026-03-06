import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import { AnimatedWord } from "./AnimatedWord";

const TEXT_MAX_WIDTH = 1600;
const WINDOW_SIZE = 12;
const SILENCE_GAP_FRAMES = 9;
const SEGMENT_CLEAR_DURATION = 10;
const BACKDROP_HEIGHT = 176;

interface WordEntry {
  word: string;
  startFrame: number;
  segment: number;
}

interface WordByWordSubtitleProps {
  words: WordEntry[];
}

export const WordByWordSubtitle: React.FC<WordByWordSubtitleProps> = ({
  words,
}) => {
  const frame = useCurrentFrame();

  // Find which words are currently visible
  const appearedWords = words.filter((w) => w.startFrame <= frame);

  if (appearedWords.length === 0) return null;

  // Detect segment transitions: if there's a gap between current segment
  // and next segment, we may need to clear
  const lastAppeared = appearedWords[appearedWords.length - 1];
  const currentSegment = lastAppeared.segment;

  // Check if we're in a segment gap (silence between segments)
  const nextWord = words.find((w) => w.startFrame > frame);
  const isInGap =
    nextWord &&
    nextWord.segment !== currentSegment &&
    frame >= lastAppeared.startFrame + SILENCE_GAP_FRAMES;

  // Segment clear fade
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

  // Determine visible window (rolling 12-word window)
  const windowStart = Math.max(0, appearedWords.length - WINDOW_SIZE);
  const visibleWords = appearedWords.slice(windowStart);

  // Words being pushed out of window
  const exitingWords =
    windowStart > 0
      ? appearedWords.slice(Math.max(0, windowStart - 1), windowStart)
      : [];

  // The active word is the last appeared word
  const activeIndex = appearedWords.length - 1;

  return (
    <div
      style={{
        position: "absolute",
        bottom: 0,
        left: 0,
        width: "100%",
        height: BACKDROP_HEIGHT,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        opacity: segmentClearOpacity,
      }}
    >
      <div
        style={{
          maxWidth: TEXT_MAX_WIDTH,
          padding: "24px 40px",
          display: "flex",
          flexWrap: "wrap",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        {/* Exiting words (overflow from window) */}
        {exitingWords.map((w, i) => (
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
