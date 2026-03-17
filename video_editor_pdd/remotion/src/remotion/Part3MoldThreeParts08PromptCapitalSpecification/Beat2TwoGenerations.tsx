import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  spring,
  useVideoConfig,
} from 'remotion';
import {
  NOZZLE_BLUE,
  CHECK_GREEN,
  MUTED_GRAY,
  PANEL_BG,
  PANEL_BORDER,
  TEXT_LIGHT,
  CODE_V1,
  CODE_V2,
} from './constants';

// ── Syntax highlighting (simplified) ──
const highlightPython = (line: string): React.ReactNode[] => {
  const parts: React.ReactNode[] = [];
  const keywords =
    /\b(class|def|return|if|not|isinstance|try|except|for|in|import|from|match|case|with)\b/g;
  const strings = /(["'])(?:(?=(\\?))\2.)*?\1|f["'].*?["']/g;
  const comments = /#.*/g;
  const decorators = /@\w+/g;
  const numbers = /\b\d+\b/g;

  // Simple approach: color the whole line based on content
  const trimmed = line.trimStart();
  if (trimmed.startsWith('#') || trimmed.startsWith('"""')) {
    return [
      <span key="c" style={{ color: '#6A9955' }}>
        {line}
      </span>,
    ];
  }
  if (trimmed.startsWith('@')) {
    return [
      <span key="d" style={{ color: '#DCDCAA' }}>
        {line}
      </span>,
    ];
  }

  // Split by keywords and strings
  let remaining = line;
  let idx = 0;

  // Token-based simple highlight
  const tokens = line.split(/(\b(?:class|def|return|if|not|isinstance|try|except|for|in|import|from|match|case|with|None|True|False|self)\b|["'].*?["']|#.*$|\d+)/);

  return tokens.map((token, ti) => {
    const kw = [
      'class', 'def', 'return', 'if', 'not', 'isinstance', 'try',
      'except', 'for', 'in', 'import', 'from', 'match', 'case', 'with',
    ];
    const constants = ['None', 'True', 'False', 'self'];

    if (kw.includes(token)) {
      return (
        <span key={ti} style={{ color: '#C586C0' }}>
          {token}
        </span>
      );
    }
    if (constants.includes(token)) {
      return (
        <span key={ti} style={{ color: '#569CD6' }}>
          {token}
        </span>
      );
    }
    if (token.startsWith('"') || token.startsWith("'") || token.startsWith('f"') || token.startsWith("f'")) {
      return (
        <span key={ti} style={{ color: '#CE9178' }}>
          {token}
        </span>
      );
    }
    if (token.startsWith('#')) {
      return (
        <span key={ti} style={{ color: '#6A9955' }}>
          {token}
        </span>
      );
    }
    if (/^\d+$/.test(token)) {
      return (
        <span key={ti} style={{ color: '#B5CEA8' }}>
          {token}
        </span>
      );
    }
    return (
      <span key={ti} style={{ color: '#D4D4D4' }}>
        {token}
      </span>
    );
  });
};

// ── Code panel ──
const CodePanel: React.FC<{
  x: number;
  y: number;
  width: number;
  height: number;
  filename: string;
  code: string;
  charsVisible: number;
  showCheckmark: boolean;
  checkScale: number;
}> = ({ x, y, width, height, filename, code, charsVisible, showCheckmark, checkScale }) => {
  const lines = code.split('\n');
  let charCount = 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height,
        backgroundColor: PANEL_BG,
        opacity: 0.85,
        border: `1px solid ${PANEL_BORDER}`,
        borderRadius: 6,
        overflow: 'hidden',
        display: 'flex',
        flexDirection: 'column',
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: 28,
          backgroundColor: '#151D2E',
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 10,
          gap: 6,
          borderBottom: `1px solid ${PANEL_BORDER}`,
          flexShrink: 0,
        }}
      >
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#EF4444',
            opacity: 0.5,
          }}
        />
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#F59E0B',
            opacity: 0.5,
          }}
        />
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#22C55E',
            opacity: 0.5,
          }}
        />
        <span
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 10,
            color: MUTED_GRAY,
            marginLeft: 8,
          }}
        >
          {filename}
        </span>
      </div>

      {/* Code content */}
      <div
        style={{
          padding: '8px 10px',
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 9,
          lineHeight: '14px',
          whiteSpace: 'pre',
          overflow: 'hidden',
          flex: 1,
        }}
      >
        {lines.map((line, li) => {
          const lineStart = charCount;
          charCount += line.length + 1; // +1 for newline
          if (lineStart >= charsVisible) return null;
          const visibleLen = Math.min(line.length, charsVisible - lineStart);
          const visibleLine = line.substring(0, visibleLen);

          return (
            <div key={li} style={{ height: 14 }}>
              {highlightPython(visibleLine)}
            </div>
          );
        })}
      </div>

      {/* Green checkmark */}
      {showCheckmark && (
        <div
          style={{
            position: 'absolute',
            right: 12,
            bottom: 12,
            width: 40,
            height: 40,
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'center',
            transform: `scale(${checkScale})`,
          }}
        >
          <svg width={40} height={40} viewBox="0 0 40 40">
            <circle cx={20} cy={20} r={18} fill={CHECK_GREEN} opacity={0.15} />
            <path
              d="M 12 20 L 18 26 L 28 14"
              stroke={CHECK_GREEN}
              strokeWidth={3}
              fill="none"
              strokeLinecap="round"
              strokeLinejoin="round"
              opacity={0.6}
            />
          </svg>
        </div>
      )}
    </div>
  );
};

export const Beat2TwoGenerations: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Panel fade-in (frame 0-30 of this beat, absolute 150-180)
  const panelOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Code typing: starts at frame 30, 2 frames per char
  const charsVisible = Math.max(0, Math.floor((frame - 30) / 2));

  // Checkmarks at frame 120 (absolute 270) — spring animation
  const checkFrame = frame - 120;
  const showCheckmark = frame >= 120;
  const checkScale = showCheckmark
    ? spring({
        frame: checkFrame,
        fps,
        config: { stiffness: 200, damping: 10 },
      })
    : 0;

  // Labels at frame 120
  const labelOpacity = interpolate(frame, [120, 135], [0, 1], {
    extrapolateRight: 'clamp',
  });

  // Caption at frame 140
  const captionOpacity = interpolate(frame, [140, 160], [0, 1], {
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill style={{ opacity: panelOpacity }}>
      <CodePanel
        x={160}
        y={200}
        width={340}
        height={500}
        filename="user_parser_v1.py"
        code={CODE_V1}
        charsVisible={charsVisible}
        showCheckmark={showCheckmark}
        checkScale={checkScale}
      />
      <CodePanel
        x={540}
        y={200}
        width={340}
        height={500}
        filename="user_parser_v2.py"
        code={CODE_V2}
        charsVisible={charsVisible}
        showCheckmark={showCheckmark}
        checkScale={checkScale}
      />

      {/* Shared prompt indicator at top */}
      <div
        style={{
          position: 'absolute',
          left: 340,
          top: 160,
          width: 360,
          textAlign: 'center',
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 10,
          color: NOZZLE_BLUE,
          opacity: panelOpacity * 0.5,
        }}
      >
        user_parser.prompt → two generations
      </div>

      {/* Center comparison labels */}
      <div
        style={{
          position: 'absolute',
          left: 510,
          top: 430,
          transform: 'translateX(-50%)',
          textAlign: 'center',
          opacity: labelOpacity,
        }}
      >
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 20,
            color: MUTED_GRAY,
            opacity: 0.4,
            marginBottom: 8,
          }}
        >
          ≠ code
        </div>
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 20,
            color: CHECK_GREEN,
            opacity: 0.6,
          }}
        >
          = behavior
        </div>
      </div>

      {/* Caption */}
      <div
        style={{
          position: 'absolute',
          left: 160,
          top: 730,
          width: 720,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          color: TEXT_LIGHT,
          opacity: captionOpacity * 0.7,
          lineHeight: '22px',
        }}
      >
        What's locked is the <strong>behavior</strong>. The code is flexible;
        the <strong>contract</strong> is fixed.
      </div>
    </AbsoluteFill>
  );
};
