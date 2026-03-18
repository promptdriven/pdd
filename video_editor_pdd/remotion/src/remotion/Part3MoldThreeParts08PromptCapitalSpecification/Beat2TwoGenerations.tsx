import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  spring,
  useVideoConfig,
} from 'remotion';
import { COLORS, CODE_A, CODE_B } from './constants';

/**
 * Beat 2 — Two Generations, Same Spec (frames 0-210 relative, 150-360 absolute)
 * Split view showing same prompt generating different code.
 * Both pass with green checkmarks.
 */

// Simple syntax highlighting for Python
const highlightPython = (code: string, visibleChars: number): React.ReactNode[] => {
  const truncated = code.slice(0, visibleChars);
  const lines = truncated.split('\n');

  const keywords = [
    'import', 'from', 'class', 'def', 'return', 'if', 'not', 'try',
    'except', 'for', 'in', 'self', 'None', 'True', 'False', 'Optional',
  ];
  const builtins = ['str', 'dict', 'bool', 'list', 'isinstance', 'int'];

  return lines.map((line, lineIdx) => {
    const parts: React.ReactNode[] = [];
    let remaining = line;
    let partKey = 0;

    // Simple token-based highlighting
    while (remaining.length > 0) {
      // Comments
      if (remaining.startsWith('#')) {
        parts.push(
          <span key={partKey++} style={{ color: '#6A9955' }}>
            {remaining}
          </span>
        );
        remaining = '';
        continue;
      }

      // Strings (double or single quoted)
      const strMatch = remaining.match(/^(["'])(?:(?!\1).)*\1/);
      if (strMatch) {
        parts.push(
          <span key={partKey++} style={{ color: '#CE9178' }}>
            {strMatch[0]}
          </span>
        );
        remaining = remaining.slice(strMatch[0].length);
        continue;
      }

      // Triple-quoted strings
      const tripleMatch = remaining.match(/^("""|''')[\s\S]*?\1/);
      if (tripleMatch) {
        parts.push(
          <span key={partKey++} style={{ color: '#CE9178' }}>
            {tripleMatch[0]}
          </span>
        );
        remaining = remaining.slice(tripleMatch[0].length);
        continue;
      }

      // Words (keywords, builtins, identifiers)
      const wordMatch = remaining.match(/^[a-zA-Z_]\w*/);
      if (wordMatch) {
        const word = wordMatch[0];
        let color = '#D4D4D4'; // default
        if (keywords.includes(word)) color = '#C586C0';
        else if (builtins.includes(word)) color = '#4EC9B0';
        else if (word.startsWith('_') || /^[A-Z]/.test(word))
          color = '#4FC1FF';

        parts.push(
          <span key={partKey++} style={{ color }}>
            {word}
          </span>
        );
        remaining = remaining.slice(word.length);
        continue;
      }

      // Decorators
      if (remaining.startsWith('@')) {
        const decMatch = remaining.match(/^@\w+/);
        if (decMatch) {
          parts.push(
            <span key={partKey++} style={{ color: '#DCDCAA' }}>
              {decMatch[0]}
            </span>
          );
          remaining = remaining.slice(decMatch[0].length);
          continue;
        }
      }

      // Other chars
      parts.push(
        <span key={partKey++} style={{ color: '#D4D4D4' }}>
          {remaining[0]}
        </span>
      );
      remaining = remaining.slice(1);
    }

    return (
      <div key={lineIdx} style={{ minHeight: 14, lineHeight: '14px' }}>
        {parts.length > 0 ? parts : '\u00A0'}
      </div>
    );
  });
};

const CodePanel: React.FC<{
  x: number;
  y: number;
  width: number;
  height: number;
  filename: string;
  code: string;
  frame: number;
  showCheckmark: boolean;
  checkmarkProgress: number;
  panelOpacity: number;
}> = ({
  x,
  y,
  width,
  height,
  filename,
  code,
  frame,
  showCheckmark,
  checkmarkProgress,
  panelOpacity,
}) => {
  // Type code at ~2 frames per char, starting at frame 30 (relative to beat start)
  const typingFrame = Math.max(0, frame - 30);
  const visibleChars = Math.floor(typingFrame / 2);

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height,
        backgroundColor: COLORS.codePanel,
        opacity: panelOpacity * 0.6,
        border: `1px solid ${COLORS.codeBorder}`,
        borderRadius: 6,
        overflow: 'hidden',
        display: 'flex',
        flexDirection: 'column',
      }}
    >
      {/* Title bar */}
      <div
        style={{
          padding: '6px 12px',
          borderBottom: `1px solid ${COLORS.codeBorder}`,
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 10,
          color: COLORS.labelMuted,
          display: 'flex',
          alignItems: 'center',
          gap: 6,
        }}
      >
        <span
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#374151',
            display: 'inline-block',
          }}
        />
        {filename}
      </div>

      {/* Code area */}
      <div
        style={{
          flex: 1,
          padding: '8px 12px',
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 10,
          overflow: 'hidden',
          position: 'relative',
        }}
      >
        {highlightPython(code, visibleChars)}
      </div>

      {/* Green checkmark */}
      {showCheckmark && (
        <div
          style={{
            position: 'absolute',
            bottom: 16,
            right: 16,
            width: 40,
            height: 40,
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'center',
            transform: `scale(${checkmarkProgress})`,
            opacity: checkmarkProgress,
          }}
        >
          <svg width={40} height={40} viewBox="0 0 40 40">
            <circle
              cx={20}
              cy={20}
              r={18}
              fill={COLORS.checkmarkGreen}
              opacity={0.6}
            />
            <polyline
              points="12,20 18,26 28,14"
              fill="none"
              stroke="white"
              strokeWidth={3}
              strokeLinecap="round"
              strokeLinejoin="round"
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

  // Panels appear at frame 0 (relative), which is frame 150 absolute
  const panelOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Checkmarks appear at frame 120 relative
  const showCheckmark = frame >= 120;
  const checkmarkProgress = showCheckmark
    ? spring({
        frame: frame - 120,
        fps,
        config: { stiffness: 200, damping: 10 },
      })
    : 0;

  // Labels appear at frame 120
  const labelsOpacity = interpolate(frame, [120, 135], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Caption appears at frame 140
  const captionOpacity = interpolate(frame, [140, 160], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill>
      {/* Left Panel: Generation A */}
      <CodePanel
        x={160}
        y={200}
        width={340}
        height={500}
        filename="user_parser_v1.py"
        code={CODE_A}
        frame={frame}
        showCheckmark={showCheckmark}
        checkmarkProgress={checkmarkProgress}
        panelOpacity={panelOpacity}
      />

      {/* Right Panel: Generation B */}
      <CodePanel
        x={540}
        y={200}
        width={340}
        height={500}
        filename="user_parser_v2.py"
        code={CODE_B}
        frame={frame}
        showCheckmark={showCheckmark}
        checkmarkProgress={checkmarkProgress}
        panelOpacity={panelOpacity}
      />

      {/* Shared prompt indicator above both panels */}
      <div
        style={{
          position: 'absolute',
          left: 160,
          top: 160,
          width: 720,
          textAlign: 'center',
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 11,
          color: COLORS.nozzleBlue,
          opacity: panelOpacity * 0.6,
        }}
      >
        user_parser.prompt → generate ×2
      </div>

      {/* Center labels: ≠ code, = behavior */}
      <div
        style={{
          position: 'absolute',
          left: 500,
          top: 430,
          width: 40,
          textAlign: 'center',
          opacity: labelsOpacity,
        }}
      >
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 20,
            color: COLORS.labelMuted,
            opacity: 0.4,
            marginBottom: 12,
          }}
        >
          ≠ code
        </div>
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 20,
            color: COLORS.behaviorGreen,
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
          top: 740,
          width: 720,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          color: COLORS.textLight,
          opacity: captionOpacity * 0.7,
          lineHeight: '22px',
        }}
      >
        What&apos;s locked is the{' '}
        <span style={{ fontWeight: 700 }}>behavior</span>. The code is flexible;
        the <span style={{ fontWeight: 700 }}>contract</span> is fixed.
      </div>
    </AbsoluteFill>
  );
};
