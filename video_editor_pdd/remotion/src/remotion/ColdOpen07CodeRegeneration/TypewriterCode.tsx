import React from 'react';
import { interpolate } from 'remotion';
import SyntaxLine from './SyntaxLine';
import {
  CLEAN_CODE_LINES,
  FPS,
  CHARS_PER_SECOND,
  ENTRANCE_GLOW_COLOR,
  ENTRANCE_GLOW_OPACITY,
  CODE_TOP_PADDING,
} from './constants';

// ── Helpers ─────────────────────────────────────────────────────────────────

/**
 * For each line, compute { charOffset, lineLength }.
 * charOffset = total chars before this line (including newlines).
 */
interface LineInfo {
  charOffset: number;
  lineLength: number;
}

function buildLineInfo(lines: string[]): LineInfo[] {
  const result: LineInfo[] = [];
  let offset = 0;
  for (const line of lines) {
    result.push({ charOffset: offset, lineLength: line.length });
    offset += line.length + 1; // +1 for the implied newline
  }
  return result;
}

// ── Component ───────────────────────────────────────────────────────────────

interface TypewriterCodeProps {
  /** Frame offset within the regeneration phase (0 = regen start) */
  phaseFrame: number;
}

const TypewriterCode: React.FC<TypewriterCodeProps> = ({
  phaseFrame,
}) => {
  const lineInfos = buildLineInfo(CLEAN_CODE_LINES);

  // Total chars typed so far (linear, 60 chars/sec at 30fps = 2 chars/frame)
  const charsPerFrame = CHARS_PER_SECOND / FPS;
  const totalTyped = Math.floor(phaseFrame * charsPerFrame);

  return (
    <div style={{ position: 'absolute', top: CODE_TOP_PADDING, left: 0, width: '100%' }}>
      {CLEAN_CODE_LINES.map((line, lineIdx) => {
        const info = lineInfos[lineIdx];
        const lineStart = info.charOffset;
        const lineEnd = lineStart + info.lineLength;

        // How many chars of this line are visible
        if (totalTyped < lineStart) return null; // line not started yet

        // For empty lines, show immediately (undefined = all chars visible)
        const visibleChars = info.lineLength === 0
          ? undefined
          : Math.min(totalTyped - lineStart, info.lineLength);

        // Has the full line been typed?
        const lineFullyTyped = totalTyped >= lineEnd;

        // Frame when this line first appeared
        const lineAppearFrame = lineStart / charsPerFrame;
        // Frame when this line was fully typed
        const lineCompleteFrame = lineEnd / charsPerFrame;

        // Entrance glow: holds while typing, then fades over 10 frames after line completes
        const glowFadeStart = lineFullyTyped ? lineCompleteFrame : phaseFrame;
        const glowFadeEnd = glowFadeStart + 10;

        let glowOpacity = 0;
        if (phaseFrame >= lineAppearFrame) {
          if (!lineFullyTyped) {
            // Still typing this line — full glow
            glowOpacity = ENTRANCE_GLOW_OPACITY;
          } else {
            // Line complete — fade out over 10 frames
            glowOpacity = interpolate(
              phaseFrame,
              [glowFadeStart, glowFadeEnd],
              [ENTRANCE_GLOW_OPACITY, 0],
              { extrapolateRight: 'clamp', extrapolateLeft: 'clamp' },
            );
          }
        }

        const bgColor =
          glowOpacity > 0
            ? `${ENTRANCE_GLOW_COLOR}${Math.round(glowOpacity * 255)
                .toString(16)
                .padStart(2, '0')}`
            : undefined;

        return (
          <SyntaxLine
            key={lineIdx}
            line={line}
            lineIndex={lineIdx}
            visibleChars={visibleChars}
            bgColor={bgColor}
            lineNumber={lineIdx + 1}
          />
        );
      })}
    </div>
  );
};

export default TypewriterCode;
