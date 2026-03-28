import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  DOC_BG,
  DOC_BORDER,
  DOC_WIDTH,
  DOC_HEIGHT,
  DOC_X,
  DOC_Y,
  DOC_PADDING,
  DOC_BORDER_RADIUS,
  DOC_FADE_START,
  DOC_FADE_DURATION,
  HEADING_COLOR,
  HEADING_SIZE,
  PROSE_COLOR,
  PROSE_SIZE,
  PROSE_LINE_HEIGHT,
  PARAGRAPH_SPACING,
  CODE_BG,
  CODE_BORDER,
  CODE_ACCENT,
  CODE_ACCENT_WIDTH,
  CODE_BORDER_RADIUS,
  CODE_TEXT_COLOR,
  CODE_SIZE,
  CODE_APPEAR_START,
  CODE_APPEAR_DURATION,
  CODE_GLOW_DURATION,
  TEXT_REVEAL_START,
  TEXT_LINE_RATE,
  BELOW_CODE_START,
  DOC_HEADING,
  PROSE_ABOVE_CODE,
  EMBEDDED_CODE,
  PROSE_BELOW_CODE,
} from './constants';

const DocumentContainer: React.FC = () => {
  const frame = useCurrentFrame();

  // Document container fade-in
  const containerOpacity = interpolate(
    frame,
    [DOC_FADE_START, DOC_FADE_START + DOC_FADE_DURATION],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // --- Text reveal for prose above code ---
  const aboveLinesTotal = 1 + PROSE_ABOVE_CODE.length; // heading + prose lines
  const aboveRevealFrame = frame - TEXT_REVEAL_START;
  const aboveLinesVisible = Math.max(
    0,
    Math.min(aboveLinesTotal, Math.floor(aboveRevealFrame / TEXT_LINE_RATE) + 1)
  );

  // --- Code block appear ---
  const codeProgress = interpolate(
    frame,
    [CODE_APPEAR_START, CODE_APPEAR_START + CODE_APPEAR_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );
  const codeScale = interpolate(codeProgress, [0, 1], [0.98, 1]);
  const codeOpacity = codeProgress;

  // Code glow
  const glowOpacity = interpolate(
    frame,
    [
      CODE_APPEAR_START + CODE_APPEAR_DURATION,
      CODE_APPEAR_START + CODE_APPEAR_DURATION + CODE_GLOW_DURATION,
    ],
    [0, 0.08],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // --- Below-code prose reveal ---
  const belowRevealFrame = frame - BELOW_CODE_START;
  const belowLinesVisible = Math.max(
    0,
    Math.min(PROSE_BELOW_CODE.length, Math.floor(belowRevealFrame / TEXT_LINE_RATE) + 1)
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: DOC_X,
        top: DOC_Y,
        width: DOC_WIDTH,
        height: DOC_HEIGHT,
        background: DOC_BG,
        border: `1px solid ${DOC_BORDER}`,
        borderRadius: DOC_BORDER_RADIUS,
        padding: DOC_PADDING,
        opacity: containerOpacity,
        overflow: 'hidden',
        boxSizing: 'border-box',
      }}
    >
      {/* Faint diagonal texture overlay */}
      <div
        style={{
          position: 'absolute',
          inset: 0,
          backgroundImage: `repeating-linear-gradient(
            135deg,
            transparent,
            transparent 10px,
            rgba(30, 41, 59, 0.02) 10px,
            rgba(30, 41, 59, 0.02) 11px
          )`,
          pointerEvents: 'none',
        }}
      />

      {/* Warm tint overlay */}
      <div
        style={{
          position: 'absolute',
          inset: 0,
          background: 'rgba(212, 197, 176, 0.03)',
          pointerEvents: 'none',
        }}
      />

      {/* Content */}
      <div style={{ position: 'relative', zIndex: 1 }}>
        {/* Heading */}
        {aboveLinesVisible >= 1 && (
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: HEADING_SIZE,
              fontWeight: 700,
              color: HEADING_COLOR,
              marginBottom: PARAGRAPH_SPACING,
              opacity: interpolate(
                aboveRevealFrame,
                [0, TEXT_LINE_RATE],
                [0, 1],
                { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
              ),
            }}
          >
            {DOC_HEADING}
          </div>
        )}

        {/* Prose above code */}
        {PROSE_ABOVE_CODE.map((line, i) => {
          const lineIndex = i + 1; // offset by heading
          if (aboveLinesVisible <= lineIndex) return null;
          const lineFrame = aboveRevealFrame - lineIndex * TEXT_LINE_RATE;
          const lineOpacity = interpolate(
            lineFrame,
            [0, TEXT_LINE_RATE],
            [0, 0.85],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );
          const isBlank = line.trim() === '';
          return (
            <div
              key={`above-${i}`}
              style={{
                fontFamily: 'Inter, sans-serif',
                fontSize: PROSE_SIZE,
                fontWeight: 400,
                color: PROSE_COLOR,
                lineHeight: PROSE_LINE_HEIGHT,
                opacity: lineOpacity,
                height: isBlank ? PARAGRAPH_SPACING : 'auto',
              }}
            >
              {isBlank ? '' : line}
            </div>
          );
        })}

        {/* Embedded code block */}
        <div
          style={{
            marginTop: PARAGRAPH_SPACING,
            marginBottom: PARAGRAPH_SPACING,
            opacity: codeOpacity,
            transform: `scale(${codeScale})`,
            transformOrigin: 'top left',
          }}
        >
          <div
            style={{
              background: CODE_BG,
              border: `1px solid ${CODE_BORDER}`,
              borderLeft: `${CODE_ACCENT_WIDTH}px solid ${CODE_ACCENT}`,
              borderRadius: CODE_BORDER_RADIUS,
              padding: '16px 20px',
              boxShadow: `0 0 8px rgba(74, 144, 217, ${glowOpacity})`,
              position: 'relative',
            }}
          >
            {EMBEDDED_CODE.map((codeLine, i) => (
              <div
                key={`code-${i}`}
                style={{
                  fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
                  fontSize: CODE_SIZE,
                  fontWeight: 400,
                  color: CODE_TEXT_COLOR,
                  lineHeight: 1.5,
                  whiteSpace: 'pre',
                }}
              >
                {codeLine}
              </div>
            ))}
          </div>
        </div>

        {/* Prose below code */}
        {PROSE_BELOW_CODE.map((line, i) => {
          if (belowLinesVisible <= i) return null;
          const lineFrame = belowRevealFrame - i * TEXT_LINE_RATE;
          const lineOpacity = interpolate(
            lineFrame,
            [0, TEXT_LINE_RATE],
            [0, 0.85],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );
          return (
            <div
              key={`below-${i}`}
              style={{
                fontFamily: 'Inter, sans-serif',
                fontSize: PROSE_SIZE,
                fontWeight: 400,
                color: PROSE_COLOR,
                lineHeight: PROSE_LINE_HEIGHT,
                opacity: lineOpacity,
              }}
            >
              {line}
            </div>
          );
        })}
      </div>
    </div>
  );
};

export default DocumentContainer;
