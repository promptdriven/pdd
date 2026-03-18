import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS } from './constants';

interface EditorWindowProps {
  x: number;
  y: number;
  width: number;
  height: number;
  filename: string;
  lines: readonly string[];
  /** If true, text uses monospace font for code; otherwise Inter for prose */
  isCode?: boolean;
  /** Animate opacity from this value... */
  opacityFrom?: number;
  /** ...to this value */
  opacityTo?: number;
  /** Frame at which opacity animation starts */
  fadeStartFrame?: number;
  /** Duration of opacity fade in frames */
  fadeDuration?: number;
  /** Border color */
  borderColor?: string;
  /** Border opacity from */
  borderOpacityFrom?: number;
  /** Border opacity to */
  borderOpacityTo?: number;
  /** Border width */
  borderWidth?: number;
  /** Glow color */
  glowColor?: string;
  /** Glow intensity from (box-shadow spread multiplier) */
  glowFrom?: number;
  /** Glow intensity to */
  glowTo?: number;
  /** Text color */
  textColor?: string;
  /** Text opacity */
  textOpacity?: number;
}

const EditorWindow: React.FC<EditorWindowProps> = ({
  x,
  y,
  width,
  height,
  filename,
  lines,
  isCode = false,
  opacityFrom = 0.5,
  opacityTo = 0.5,
  fadeStartFrame = 0,
  fadeDuration = 1,
  borderColor = COLORS.codeBorder,
  borderOpacityFrom = 0.3,
  borderOpacityTo = 0.3,
  borderWidth = 1,
  glowColor,
  glowFrom = 0,
  glowTo = 0,
  textColor = COLORS.codeText,
  textOpacity = 0.5,
}) => {
  const frame = useCurrentFrame();

  const contentOpacity = interpolate(
    frame,
    [fadeStartFrame, fadeStartFrame + fadeDuration],
    [opacityFrom, opacityTo],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
  );

  const borderOp = interpolate(
    frame,
    [fadeStartFrame, fadeStartFrame + fadeDuration],
    [borderOpacityFrom, borderOpacityTo],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
  );

  const glowIntensity = glowColor
    ? interpolate(
        frame,
        [fadeStartFrame, fadeStartFrame + fadeDuration],
        [glowFrom, glowTo],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
      )
    : 0;

  const fontFamily = isCode ? '"JetBrains Mono", monospace' : '"Inter", sans-serif';

  // Parse hex color to rgba
  const hexToRgba = (hex: string, alpha: number) => {
    const r = parseInt(hex.slice(1, 3), 16);
    const g = parseInt(hex.slice(3, 5), 16);
    const b = parseInt(hex.slice(5, 7), 16);
    return `rgba(${r}, ${g}, ${b}, ${alpha})`;
  };

  const boxShadow = glowColor && glowIntensity > 0
    ? `0 0 ${16 * glowIntensity / 0.06}px ${8 * glowIntensity / 0.06}px ${hexToRgba(glowColor, glowIntensity)}`
    : 'none';

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height,
        borderRadius: 6,
        overflow: 'hidden',
        border: `${borderWidth}px solid ${hexToRgba(borderColor, borderOp)}`,
        boxShadow,
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: 24,
          backgroundColor: COLORS.titleBar,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 10,
          gap: 6,
        }}
      >
        {/* Window dots */}
        <div style={{ width: 6, height: 6, borderRadius: 3, backgroundColor: '#EF4444', opacity: 0.6 }} />
        <div style={{ width: 6, height: 6, borderRadius: 3, backgroundColor: '#F59E0B', opacity: 0.6 }} />
        <div style={{ width: 6, height: 6, borderRadius: 3, backgroundColor: '#22C55E', opacity: 0.6 }} />
        <span
          style={{
            marginLeft: 8,
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 9,
            color: COLORS.codeText,
            opacity: 0.6,
          }}
        >
          {filename}
        </span>
      </div>

      {/* Editor content */}
      <div
        style={{
          backgroundColor: COLORS.editorBg,
          padding: '8px 10px',
          height: height - 24,
          overflow: 'hidden',
        }}
      >
        {lines.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily,
              fontSize: 9,
              lineHeight: '13px',
              color: textColor,
              opacity: contentOpacity * (textOpacity / 0.5),
              whiteSpace: 'pre',
            }}
          >
            {line || '\u00A0'}
          </div>
        ))}
      </div>
    </div>
  );
};

export default EditorWindow;
