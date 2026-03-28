import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  BG_COLOR,
  PROMPT_LINES,
  EDITOR_HEIGHT,
  TITLE_BAR_HEIGHT,
  LINE_HEIGHT,
  CONTENT_REVEAL_START,
  LINES_PER_FRAME,
  LABEL_FADE_IN_START,
  LABEL_FADE_IN_DURATION,
  FINAL_FADE_START,
  FINAL_FADE_DURATION,
  ACCENT_AMBER,
} from './constants';
import { EditorChrome } from './EditorChrome';
import { PromptLine } from './PromptLine';

export const defaultPart4PrecisionTradeoff04DetailedPromptFileProps = {};

export const Part4PrecisionTradeoff04DetailedPromptFile: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Label fade-in ────────────────────────────────────────────────
  const labelOpacity = interpolate(
    frame,
    [LABEL_FADE_IN_START, LABEL_FADE_IN_START + LABEL_FADE_IN_DURATION],
    [0, 0.7],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Final fade-out ───────────────────────────────────────────────
  const fadeOut = interpolate(
    frame,
    [FINAL_FADE_START, FINAL_FADE_START + FINAL_FADE_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // ── Content scroll ───────────────────────────────────────────────
  // Total content height exceeds the editor body, so we scroll
  const totalContentHeight = PROMPT_LINES.length * LINE_HEIGHT;
  const editorBodyHeight = EDITOR_HEIGHT - TITLE_BAR_HEIGHT;
  const maxScroll = Math.max(0, totalContentHeight - editorBodyHeight + 40);

  // Start scrolling after initial lines fill the view
  const linesVisibleInBody = Math.floor(editorBodyHeight / LINE_HEIGHT);
  const frameWhenBodyFull =
    CONTENT_REVEAL_START + linesVisibleInBody / LINES_PER_FRAME;

  // Scroll starts when body is full, ends when all lines have been revealed
  const lastLineRevealFrame =
    CONTENT_REVEAL_START + PROMPT_LINES.length / LINES_PER_FRAME;
  const scrollEndFrame = Math.min(lastLineRevealFrame + 10, 150);

  const scrollOffset =
    frameWhenBodyFull < scrollEndFrame
      ? interpolate(
          frame,
          [frameWhenBodyFull, scrollEndFrame],
          [0, maxScroll],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }
        )
      : 0;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <div style={{ opacity: fadeOut, width: '100%', height: '100%' }}>
        {/* Editor window */}
        <EditorChrome>
          <div
            style={{
              padding: '10px 12px 10px 6px',
              transform: `translateY(-${scrollOffset}px)`,
              willChange: 'transform',
            }}
          >
            {PROMPT_LINES.map((line, i) => (
              <PromptLine
                key={line.lineNumber}
                lineNumber={line.lineNumber}
                text={line.text}
                index={i}
                isHighlight={line.isHighlight}
                section={line.section}
              />
            ))}
          </div>
        </EditorChrome>

        {/* Bottom label */}
        <div
          style={{
            position: 'absolute',
            bottom: 80,
            left: 0,
            right: 0,
            display: 'flex',
            justifyContent: 'center',
            opacity: labelOpacity,
          }}
        >
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 15,
              fontWeight: 400,
              color: ACCENT_AMBER,
            }}
          >
            Without tests: prompt must specify everything
          </span>
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff04DetailedPromptFile;
