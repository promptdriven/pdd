import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  EDITOR_BG,
  TEXT_PRIMARY,
  COLOR_SURFACE0,
  COLOR_OVERLAY0,
  CODE_FONT,
  CODE_FONT_SIZE,
  CODE_LINE_HEIGHT,
  PANEL_BORDER_RADIUS,
  TITLE_BAR_HEIGHT,
  PANEL_PADDING_X,
  PANEL_PADDING_Y,
  COLOR_YELLOW,
  COLOR_BLUE,
  COLOR_MAUVE,
  COLOR_PEACH,
  COLOR_GREEN,
  COLOR_TEAL,
  COLOR_RED,
  EMAIL_VALIDATOR_V1,
  EMAIL_VALIDATOR_V2,
  PHASE_HIGHLIGHT_START,
  PHASE_HIGHLIGHT_END,
  PHASE_REGEN_START,
  PHASE_REGEN_END,
} from './constants';

interface CodeEditorPanelProps {
  width: number;
  height: number;
}

/** Simple Python syntax highlighting with Catppuccin Mocha colors. */
function highlightPythonLine(line: string): React.ReactNode[] {
  const tokens: React.ReactNode[] = [];
  let remaining = line;
  let key = 0;

  const rules: Array<{ regex: RegExp; color: string }> = [
    // Comments
    { regex: /^(#.*)/, color: COLOR_OVERLAY0 },
    // Strings (triple-quoted, double, single)
    { regex: /^("""[\s\S]*?"""|'''[\s\S]*?'''|"[^"]*"|'[^']*')/, color: COLOR_GREEN },
    // Keywords
    {
      regex: /^(import|from|def|class|return|if|elif|else|try|except|raise|not|or|and|is|in|as|with|for|while|None|True|False)\b/,
      color: COLOR_MAUVE,
    },
    // Decorators
    { regex: /^(@\w+)/, color: COLOR_YELLOW },
    // Function calls
    { regex: /^(\w+)(?=\()/, color: COLOR_BLUE },
    // Numbers
    { regex: /^(\d+)/, color: COLOR_PEACH },
    // Operators / punctuation
    { regex: /^([=+\-*/<>!|&^~%:.,()[\]{}]+)/, color: COLOR_TEAL },
    // Identifiers
    { regex: /^(\w+)/, color: TEXT_PRIMARY },
    // Whitespace
    { regex: /^(\s+)/, color: TEXT_PRIMARY },
  ];

  while (remaining.length > 0) {
    let matched = false;
    for (const rule of rules) {
      const match = remaining.match(rule.regex);
      if (match) {
        tokens.push(
          <span key={key++} style={{ color: rule.color }}>
            {match[1]}
          </span>
        );
        remaining = remaining.slice(match[1].length);
        matched = true;
        break;
      }
    }
    if (!matched) {
      tokens.push(
        <span key={key++} style={{ color: TEXT_PRIMARY }}>
          {remaining[0]}
        </span>
      );
      remaining = remaining.slice(1);
    }
  }
  return tokens;
}

export const CodeEditorPanel: React.FC<CodeEditorPanelProps> = ({
  width,
  height,
}) => {
  const frame = useCurrentFrame();

  // Determine which code version to show
  const showV2 = frame >= PHASE_REGEN_END;
  const inRegen = frame >= PHASE_REGEN_START && frame < PHASE_REGEN_END;

  const codeText = showV2 ? EMAIL_VALIDATOR_V2 : EMAIL_VALIDATOR_V1;
  const lines = codeText.split('\n');

  // Code opacity during regen shimmer: dips to 0.3 and back
  const codeOpacity = inRegen
    ? interpolate(
        frame,
        [PHASE_REGEN_START, PHASE_REGEN_START + 15, PHASE_REGEN_END - 15, PHASE_REGEN_END],
        [1, 0.3, 0.3, 1],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      )
    : 1;

  // Highlight glow for new test_unicode_domain lines (in V1, lines ~14-17 area, simulated)
  const highlightActive =
    frame >= PHASE_HIGHLIGHT_START && frame < PHASE_HIGHLIGHT_END;
  const highlightOpacity = highlightActive
    ? interpolate(
        frame,
        [PHASE_HIGHLIGHT_START, PHASE_HIGHLIGHT_START + 15, PHASE_HIGHLIGHT_END - 5, PHASE_HIGHLIGHT_END],
        [0, 0.15, 0.15, 0],
        {
          easing: Easing.out(Easing.quad),
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        }
      )
    : 0;

  // The "new test" is conceptually at the end of the file
  const highlightStartLine = lines.length - 5;
  const highlightEndLine = lines.length;

  const contentHeight = height - TITLE_BAR_HEIGHT;

  return (
    <div
      style={{
        width,
        height,
        backgroundColor: EDITOR_BG,
        borderRadius: PANEL_BORDER_RADIUS,
        overflow: 'hidden',
        display: 'flex',
        flexDirection: 'column',
        position: 'relative',
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: TITLE_BAR_HEIGHT,
          backgroundColor: COLOR_SURFACE0,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 14,
          paddingRight: 14,
          gap: 8,
          flexShrink: 0,
        }}
      >
        {/* Window dots */}
        <div style={{ display: 'flex', gap: 6 }}>
          {['#F38BA8', '#F9E2AF', '#A6E3A1'].map((dotColor, i) => (
            <div
              key={i}
              style={{
                width: 10,
                height: 10,
                borderRadius: '50%',
                backgroundColor: dotColor,
                opacity: 0.8,
              }}
            />
          ))}
        </div>
        <span
          style={{
            fontFamily: CODE_FONT,
            fontSize: 12,
            color: TEXT_PRIMARY,
            marginLeft: 8,
            opacity: 0.85,
          }}
        >
          email_validator.py
        </span>
      </div>

      {/* Code area */}
      <div
        style={{
          flex: 1,
          padding: `${PANEL_PADDING_Y}px ${PANEL_PADDING_X}px`,
          overflow: 'hidden',
          position: 'relative',
          opacity: codeOpacity,
        }}
      >
        {/* Line highlight */}
        {highlightOpacity > 0 && (
          <div
            style={{
              position: 'absolute',
              left: 0,
              right: 0,
              top:
                PANEL_PADDING_Y +
                highlightStartLine * CODE_FONT_SIZE * CODE_LINE_HEIGHT,
              height:
                (highlightEndLine - highlightStartLine) *
                CODE_FONT_SIZE *
                CODE_LINE_HEIGHT,
              backgroundColor: COLOR_YELLOW,
              opacity: highlightOpacity,
              pointerEvents: 'none',
            }}
          />
        )}

        {/* Code lines */}
        {lines.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: CODE_FONT,
              fontSize: CODE_FONT_SIZE,
              lineHeight: CODE_LINE_HEIGHT,
              whiteSpace: 'pre',
              display: 'flex',
            }}
          >
            {/* Line number */}
            <span
              style={{
                color: COLOR_OVERLAY0,
                width: 32,
                textAlign: 'right',
                marginRight: 12,
                opacity: 0.5,
                flexShrink: 0,
                userSelect: 'none',
              }}
            >
              {i + 1}
            </span>
            {/* Code content */}
            <span>{highlightPythonLine(line)}</span>
          </div>
        ))}
      </div>
    </div>
  );
};

export default CodeEditorPanel;
