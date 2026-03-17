import React from "react";
import { useCurrentFrame, Easing, interpolate } from "remotion";
import {
  COLORS,
  QUOTE_TEXT,
  HIGHLIGHT_PHRASES,
  FRAMES,
} from "./constants";

/**
 * Renders the quote text with word-by-word typing animation.
 * After typing completes, highlighted phrases shift to their accent colors.
 */

type WordSpan = {
  word: string;
  highlightColor: string | null;
  italic: boolean;
  dimmed: boolean;
};

function buildWordSpans(text: string): WordSpan[] {
  const words = text.split(/\s+/);
  const spans: WordSpan[] = words.map((w) => ({
    word: w,
    highlightColor: null,
    italic: false,
    dimmed: false,
  }));

  // Tag words that belong to highlighted phrases
  const lowerText = text.toLowerCase();
  for (const phrase of HIGHLIGHT_PHRASES) {
    const phraseWords = phrase.text.toLowerCase().split(/\s+/);
    const startIdx = findWordSequence(
      words.map((w) => w.toLowerCase().replace(/[.,!?;:'"]/g, "")),
      phraseWords.map((w) => w.replace(/[.,!?;:'"]/g, ""))
    );
    if (startIdx >= 0) {
      for (let i = startIdx; i < startIdx + phraseWords.length; i++) {
        spans[i].highlightColor = phrase.color;
        spans[i].italic = !!phrase.italic;
        spans[i].dimmed = !!phrase.dimmed;
      }
    }
  }

  return spans;
}

function findWordSequence(haystack: string[], needle: string[]): number {
  for (let i = 0; i <= haystack.length - needle.length; i++) {
    let match = true;
    for (let j = 0; j < needle.length; j++) {
      if (!haystack[i + j].startsWith(needle[j])) {
        match = false;
        break;
      }
    }
    if (match) return i;
  }
  return -1;
}

const WORD_SPANS = buildWordSpans(QUOTE_TEXT);

export const QuoteTyper: React.FC = () => {
  const frame = useCurrentFrame();

  // Word-by-word reveal relative to quoteStart
  const quoteLocalFrame = frame - FRAMES.quoteStart;

  // Highlight transition progress (0→1)
  const highlightProgress = interpolate(
    frame,
    [FRAMES.highlightStart, FRAMES.highlightStart + FRAMES.highlightDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: 360,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
      }}
    >
      <div
        style={{
          maxWidth: 1000,
          textAlign: "center",
          lineHeight: 1.6,
          fontFamily: "Inter, sans-serif",
          fontSize: 32,
        }}
      >
        {WORD_SPANS.map((span, idx) => {
          // Each word fades in over 4 frames
          const wordAppearFrame = idx * FRAMES.wordsPerFrame;
          const wordOpacity =
            quoteLocalFrame < wordAppearFrame
              ? 0
              : interpolate(
                  quoteLocalFrame,
                  [wordAppearFrame, wordAppearFrame + 4],
                  [0, 1],
                  {
                    extrapolateLeft: "clamp",
                    extrapolateRight: "clamp",
                    easing: Easing.out(Easing.quad),
                  }
                );

          // Color: starts white, transitions to highlight if applicable
          const baseColor = COLORS.quoteText;
          const targetColor = span.highlightColor ?? baseColor;

          // Interpolate RGB channels for color transition
          const currentColor =
            span.highlightColor && highlightProgress > 0
              ? lerpColor(baseColor, targetColor, highlightProgress)
              : baseColor;

          const baseOpacity = 0.85;
          const finalOpacity =
            span.highlightColor
              ? interpolate(highlightProgress, [0, 1], [baseOpacity, span.dimmed ? 0.8 : 1.0], {
                  extrapolateLeft: "clamp",
                  extrapolateRight: "clamp",
                })
              : baseOpacity;

          const fontWeight =
            span.highlightColor && highlightProgress > 0.5 ? 600 : 400;

          // Glow shadow for highlighted words
          const glowOpacity =
            span.highlightColor
              ? interpolate(
                  frame,
                  [FRAMES.highlightStart, FRAMES.highlightStart + 15],
                  [0, 0.15],
                  { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
                )
              : 0;

          const textShadow =
            glowOpacity > 0
              ? `0 0 4px ${span.highlightColor}${Math.round(glowOpacity * 255)
                  .toString(16)
                  .padStart(2, "0")}`
              : "none";

          return (
            <span
              key={idx}
              style={{
                opacity: wordOpacity * finalOpacity,
                color: currentColor,
                fontWeight,
                fontStyle: span.italic && highlightProgress > 0.5 ? "italic" : "normal",
                textShadow,
                transition: "none",
              }}
            >
              {span.word}
              {idx < WORD_SPANS.length - 1 ? " " : ""}
            </span>
          );
        })}
      </div>
    </div>
  );
};

/** Linear interpolation between two hex colors */
function lerpColor(a: string, b: string, t: number): string {
  const ar = parseInt(a.slice(1, 3), 16);
  const ag = parseInt(a.slice(3, 5), 16);
  const ab = parseInt(a.slice(5, 7), 16);
  const br = parseInt(b.slice(1, 3), 16);
  const bg = parseInt(b.slice(3, 5), 16);
  const bb = parseInt(b.slice(5, 7), 16);
  const r = Math.round(ar + (br - ar) * t);
  const g = Math.round(ag + (bg - ag) * t);
  const bv = Math.round(ab + (bb - ab) * t);
  return `#${r.toString(16).padStart(2, "0")}${g.toString(16).padStart(2, "0")}${bv.toString(16).padStart(2, "0")}`;
}
