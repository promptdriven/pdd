import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CodeLine,
  PATCHED_CODE,
  CLEAN_CODE,
  GUTTER_WIDTH,
  LINE_HEIGHT,
  CODE_FONT_SIZE,
  CODE_PADDING_LEFT,
  CODE_PADDING_TOP,
  LINE_NUMBER_COLOR,
  PHASE_DELETE_START,
  PHASE_DELETE_END,
  PHASE_VOID_END,
  PHASE_REGEN_START,
  PHASE_REGEN_END,
  REGEN_LINE_COUNT,
} from './constants';

interface CodeTokenSpanProps {
  line: CodeLine;
}

const CodeTokenSpan: React.FC<CodeTokenSpanProps> = ({ line }) => (
  <span>
    {line.map((token, j) => (
      <span key={j} style={{ color: token.color }}>
        {token.text}
      </span>
    ))}
  </span>
);

interface LineNumberProps {
  num: number;
}

const LineNumber: React.FC<LineNumberProps> = ({ num }) => (
  <span
    style={{
      display: 'inline-block',
      width: GUTTER_WIDTH - CODE_PADDING_LEFT,
      textAlign: 'right',
      color: LINE_NUMBER_COLOR,
      paddingRight: 12,
      userSelect: 'none',
    }}
  >
    {num}
  </span>
);

/**
 * Renders the code lines — patched code that deletes, then clean code that flows in.
 */
export const CodeLines: React.FC = () => {
  const frame = useCurrentFrame();

  // Delete animation: scale Y to 0 (lines collapse)
  const deleteProgress = interpolate(
    frame,
    [PHASE_DELETE_START, PHASE_DELETE_END],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // Which phase are we in?
  const showPatched = frame < PHASE_DELETE_END;
  const showVoid = frame >= PHASE_DELETE_END && frame < PHASE_VOID_END;
  const showRegen = frame >= PHASE_VOID_END;

  // How many regenerated lines are visible
  const regenLinesVisible = showRegen
    ? Math.min(
        Math.floor(
          interpolate(
            frame,
            [PHASE_REGEN_START, PHASE_REGEN_END],
            [0, REGEN_LINE_COUNT],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          )
        ),
        REGEN_LINE_COUNT
      )
    : 0;

  const codeFont: React.CSSProperties = {
    fontFamily: '"JetBrains Mono", "Fira Code", "Cascadia Code", monospace',
    fontSize: CODE_FONT_SIZE,
    lineHeight: `${LINE_HEIGHT}px`,
    whiteSpace: 'pre',
  };

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
      }}
    >
      {/* Patched code (visible until delete completes) */}
      {showPatched && (
        <div
          style={{
            position: 'absolute',
            top: CODE_PADDING_TOP,
            left: CODE_PADDING_LEFT,
            transformOrigin: 'top left',
            transform: frame >= PHASE_DELETE_START ? `scaleY(${deleteProgress})` : undefined,
            opacity: deleteProgress,
            ...codeFont,
          }}
        >
          {PATCHED_CODE.map((line, i) => (
            <div key={i} style={{ height: LINE_HEIGHT, display: 'flex', alignItems: 'center' }}>
              <LineNumber num={i + 1} />
              <CodeTokenSpan line={line} />
            </div>
          ))}
        </div>
      )}

      {/* Void: just the function signature */}
      {showVoid && (
        <div
          style={{
            position: 'absolute',
            top: CODE_PADDING_TOP,
            left: CODE_PADDING_LEFT,
            ...codeFont,
          }}
        >
          <div style={{ height: LINE_HEIGHT, display: 'flex', alignItems: 'center' }}>
            <LineNumber num={1} />
            <CodeTokenSpan line={PATCHED_CODE[0]} />
          </div>
          <div style={{ height: LINE_HEIGHT, display: 'flex', alignItems: 'center' }}>
            <LineNumber num={2} />
            <CodeTokenSpan line={[{ text: '    pass', color: '#CBA6F7' }]} />
          </div>
        </div>
      )}

      {/* Regenerated code flowing in */}
      {showRegen && (
        <div
          style={{
            position: 'absolute',
            top: CODE_PADDING_TOP,
            left: CODE_PADDING_LEFT,
            ...codeFont,
          }}
        >
          {CLEAN_CODE.slice(0, regenLinesVisible).map((line, i) => {
            // Each line has its own easeOut entrance
            const lineAppearFrame = PHASE_REGEN_START + i;
            const lineOpacity = interpolate(
              frame,
              [lineAppearFrame, lineAppearFrame + 3],
              [0, 1],
              {
                extrapolateLeft: 'clamp',
                extrapolateRight: 'clamp',
                easing: Easing.out(Easing.cubic),
              }
            );
            const lineTranslateY = interpolate(
              frame,
              [lineAppearFrame, lineAppearFrame + 3],
              [8, 0],
              {
                extrapolateLeft: 'clamp',
                extrapolateRight: 'clamp',
                easing: Easing.out(Easing.cubic),
              }
            );

            return (
              <div
                key={i}
                style={{
                  height: LINE_HEIGHT,
                  display: 'flex',
                  alignItems: 'center',
                  opacity: lineOpacity,
                  transform: `translateY(${lineTranslateY}px)`,
                }}
              >
                <LineNumber num={i + 1} />
                <CodeTokenSpan line={line} />
              </div>
            );
          })}
        </div>
      )}
    </div>
  );
};

export default CodeLines;
