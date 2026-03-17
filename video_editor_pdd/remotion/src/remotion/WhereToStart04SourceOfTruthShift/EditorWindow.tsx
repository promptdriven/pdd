import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TIMING } from './constants';

interface EditorWindowProps {
  x: number;
  y: number;
  width: number;
  height: number;
  filename: string;
  lines: string[];
  isCode: boolean;
  /** If true, desaturates over time */
  desaturate?: boolean;
  /** If true, applies glowing border effect */
  glow?: boolean;
}

export const EditorWindow: React.FC<EditorWindowProps> = ({
  x,
  y,
  width,
  height,
  filename,
  lines,
  isCode,
  desaturate = false,
  glow = false,
}) => {
  const frame = useCurrentFrame();

  // Code desaturation animation
  const contentOpacity = desaturate
    ? interpolate(
        frame,
        [TIMING.desaturationStart, TIMING.desaturationStart + TIMING.desaturationDuration],
        [0.5, 0.2],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
      )
    : 0.7;

  const borderOpacity = desaturate
    ? interpolate(
        frame,
        [TIMING.desaturationStart, TIMING.desaturationStart + TIMING.desaturationDuration],
        [0.3, 0.1],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
      )
    : 0.3;

  // Prompt glow intensification
  const glowIntensity = glow
    ? interpolate(
        frame,
        [TIMING.desaturationStart, TIMING.desaturationStart + TIMING.desaturationDuration],
        [0.06, 0.12],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
      )
    : 0;

  const glowBlur = glow ? 16 : 0;

  const textColor = desaturate
    ? interpolate(
        frame,
        [TIMING.desaturationStart, TIMING.desaturationStart + TIMING.desaturationDuration],
        [0, 1],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
      )
    : 0;

  // Interpolate between initial and final code colors
  const codeColorR = Math.round(148 + (100 - 148) * textColor);
  const codeColorG = Math.round(163 + (116 - 163) * textColor);
  const codeColorB = Math.round(184 + (139 - 184) * textColor);
  const computedTextColor = desaturate
    ? `rgb(${codeColorR}, ${codeColorG}, ${codeColorB})`
    : COLORS.promptText;

  const borderColor = desaturate
    ? `rgba(51, 65, 85, ${borderOpacity})`
    : `rgba(74, 144, 217, ${borderOpacity})`;

  const titleBarHeight = 28;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height: height + titleBarHeight,
        borderRadius: 8,
        overflow: 'hidden',
        border: glow ? `2px solid ${borderColor}` : `1px solid ${borderColor}`,
        boxShadow: glow
          ? `0 0 ${glowBlur}px rgba(74, 144, 217, ${glowIntensity}), 0 0 ${glowBlur * 2}px rgba(74, 144, 217, ${glowIntensity * 0.5})`
          : 'none',
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: titleBarHeight,
          backgroundColor: COLORS.titleBar,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 10,
          paddingRight: 10,
          gap: 6,
        }}
      >
        {/* Traffic lights */}
        {COLORS.titleBarDots.map((color, i) => (
          <div
            key={i}
            style={{
              width: 8,
              height: 8,
              borderRadius: '50%',
              backgroundColor: color,
              opacity: 0.6,
            }}
          />
        ))}
        <div
          style={{
            flex: 1,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 10,
            color: COLORS.titleBarText,
            opacity: 0.6,
          }}
        >
          {filename}
        </div>
      </div>

      {/* Editor content */}
      <div
        style={{
          backgroundColor: COLORS.editorBg,
          padding: '8px 12px',
          height: height,
          overflow: 'hidden',
        }}
      >
        {lines.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: isCode ? '"JetBrains Mono", monospace' : 'Inter, sans-serif',
              fontSize: 9,
              lineHeight: '13px',
              color: computedTextColor,
              opacity: contentOpacity,
              whiteSpace: 'pre',
            }}
          >
            {isCode && (
              <span style={{ color: COLORS.codeTextFinal, opacity: 0.3, marginRight: 8, display: 'inline-block', width: 16, textAlign: 'right' }}>
                {i + 1}
              </span>
            )}
            {line || '\u00A0'}
          </div>
        ))}
      </div>
    </div>
  );
};

export default EditorWindow;
