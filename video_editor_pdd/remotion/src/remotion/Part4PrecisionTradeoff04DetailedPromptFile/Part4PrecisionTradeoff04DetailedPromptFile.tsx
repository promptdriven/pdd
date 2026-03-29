import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  ACCENT_AMBER,
  SANS_FONT,
  LABEL_FONT_SIZE,
  PROMPT_LINES,
  LINE_HEIGHT,
  TOTAL_LINES,
  WINDOW_FADE_IN_END,
  CONTENT_REVEAL_START,
  CONTENT_LINES_PER_FRAME,
  LABEL_FADE_IN_START,
  LABEL_FADE_IN_DURATION,
  FADE_OUT_START,
  FADE_OUT_DURATION,
  EDITOR_HEIGHT,
  TITLE_BAR_HEIGHT,
} from "./constants";
import { EditorWindow } from "./EditorWindow";
import { PromptLine } from "./PromptLine";

// ── Default props (required export) ─────────────────────────────────────────
export const defaultPart4PrecisionTradeoff04DetailedPromptFileProps = {};

// ── Scroll-revealing content ────────────────────────────────────────────────

const PromptContent: React.FC = () => {
  const frame = useCurrentFrame();

  // How many lines have been revealed so far (linear scroll)
  const framesSinceRevealStart = Math.max(0, frame - CONTENT_REVEAL_START);
  const revealedLineCount = Math.min(
    TOTAL_LINES,
    Math.floor(framesSinceRevealStart * CONTENT_LINES_PER_FRAME)
  );

  // Compute the content area height (editor minus title bar)
  const contentAreaHeight = EDITOR_HEIGHT - TITLE_BAR_HEIGHT;
  // Total content height if all lines were shown
  const totalContentHeight = TOTAL_LINES * LINE_HEIGHT;

  // When total content exceeds container, scroll it up
  // We want the latest revealed lines to be visible at the bottom
  const visibleLines = Math.floor(contentAreaHeight / LINE_HEIGHT);
  const scrollOffset =
    revealedLineCount > visibleLines
      ? (revealedLineCount - visibleLines) * LINE_HEIGHT
      : 0;

  return (
    <div
      style={{
        position: "absolute",
        top: 8 - scrollOffset,
        left: 0,
        right: 0,
        height: totalContentHeight + 16,
      }}
    >
      {PROMPT_LINES.map((line, index) => {
        const lineIndex = index; // 0-based
        // Each line's gutter indicator animates when that line is revealed
        const lineRevealFrame =
          CONTENT_REVEAL_START + lineIndex / CONTENT_LINES_PER_FRAME;

        return (
          <PromptLine
            key={line.lineNumber}
            lineNumber={line.lineNumber}
            text={line.text}
            isHighlighted={line.isHighlighted}
            gutterAnimStartFrame={lineRevealFrame}
            yOffset={lineIndex * LINE_HEIGHT}
            isVisible={lineIndex < revealedLineCount}
          />
        );
      })}
    </div>
  );
};

// ── Main component ──────────────────────────────────────────────────────────

export const Part4PrecisionTradeoff04DetailedPromptFile: React.FC = () => {
  const frame = useCurrentFrame();
  const { durationInFrames } = useVideoConfig();

  // ── Window fade-in (0 → 30 frames) ──
  // Start at 0.15 so content is immediately visible at frame 0
  const windowOpacity = interpolate(
    frame,
    [0, WINDOW_FADE_IN_END],
    [0.15, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Label fade-in (180 → 200) ──
  const labelOpacity = interpolate(
    frame,
    [LABEL_FADE_IN_START, LABEL_FADE_IN_START + LABEL_FADE_IN_DURATION],
    [0, 0.78],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Final fade-out (210 → 240) ──
  const fadeOutEnd = Math.min(
    FADE_OUT_START + FADE_OUT_DURATION,
    durationInFrames
  );
  const masterOpacity = interpolate(
    frame,
    [FADE_OUT_START, fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: masterOpacity,
      }}
    >
      {/* Editor window with content */}
      <div style={{ opacity: windowOpacity }}>
        <EditorWindow>
          <PromptContent />
        </EditorWindow>
      </div>

      {/* Bottom label */}
      <div
        style={{
          position: "absolute",
          bottom: 120,
          left: 0,
          right: 0,
          textAlign: "center",
          fontFamily: SANS_FONT,
          fontSize: LABEL_FONT_SIZE,
          color: ACCENT_AMBER,
          opacity: labelOpacity,
        }}
      >
        Without tests: prompt must specify everything
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff04DetailedPromptFile;
