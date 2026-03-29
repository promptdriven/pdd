import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface PromptDocumentProps {
  lines: string[];
  headerColor: string;
  textColor: string;
  panelBg: string;
  auraColor: string;
  auraOpacity: number;
  auraBlur: number;
  x: number;
  y: number;
  width: number;
  padding: number;
  borderRadius: number;
  fadeStartFrame: number;
  fadeDuration: number;
  morphProgress: number; // 0 = normal, 1 = morphed
}

const PromptDocument: React.FC<PromptDocumentProps> = ({
  lines,
  headerColor,
  textColor,
  panelBg,
  auraColor,
  auraOpacity,
  auraBlur,
  x,
  y,
  width,
  padding,
  borderRadius,
  fadeStartFrame,
  fadeDuration,
  morphProgress,
}) => {
  const frame = useCurrentFrame();
  const relativeFrame = frame - fadeStartFrame;

  // Panel fade-in
  const panelOpacity = interpolate(
    relativeFrame,
    [0, fadeDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Slide from left
  const slideX = interpolate(
    relativeFrame,
    [0, fadeDuration],
    [-40, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Header appearance
  const headerOpacity = interpolate(
    relativeFrame,
    [5, 20],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Lines populate over time (staggered)
  const visibleLines = Math.floor(
    interpolate(
      relativeFrame,
      [10, fadeDuration + 30],
      [0, lines.length],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
    )
  );

  // Aura builds up
  const currentAuraOpacity = interpolate(
    relativeFrame,
    [fadeDuration, fadeDuration + 30],
    [0, auraOpacity],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Morph effect: slight glow pulse and text shift
  const morphGlow = interpolate(
    morphProgress,
    [0, 0.5, 1],
    [1, 1.3, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const morphHue = interpolate(
    morphProgress,
    [0, 0.5, 1],
    [0, 15, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  if (relativeFrame < 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: x + slideX,
        top: y,
        width,
        opacity: panelOpacity,
        filter: `hue-rotate(${morphHue}deg)`,
      }}
    >
      {/* Amber aura */}
      <div
        style={{
          position: 'absolute',
          inset: -auraBlur,
          borderRadius: borderRadius + auraBlur,
          background: auraColor,
          opacity: currentAuraOpacity * morphGlow,
          filter: `blur(${auraBlur}px)`,
          pointerEvents: 'none',
        }}
      />

      {/* Panel */}
      <div
        style={{
          position: 'relative',
          background: panelBg,
          borderRadius,
          padding,
          overflow: 'hidden',
        }}
      >
        {/* Header */}
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 12,
            fontWeight: 700,
            color: headerColor,
            letterSpacing: 3,
            marginBottom: 16,
            opacity: headerOpacity,
          }}
        >
          PROMPT
        </div>

        {/* Prompt lines */}
        <div style={{ fontFamily: 'Inter, sans-serif', fontSize: 14, lineHeight: '22px' }}>
          {lines.map((line, i) => (
            <div
              key={i}
              style={{
                color: textColor,
                opacity: i < visibleLines ? 0.92 : 0,
                transition: 'opacity 0.1s',
                minHeight: line === '' ? 11 : undefined,
                whiteSpace: 'pre-wrap',
              }}
            >
              {line || '\u00A0'}
            </div>
          ))}
        </div>
      </div>
    </div>
  );
};

export default PromptDocument;
