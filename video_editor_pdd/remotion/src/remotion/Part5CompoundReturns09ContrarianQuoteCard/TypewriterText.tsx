import React from 'react';
import { useCurrentFrame } from 'remotion';

interface TypewriterTextProps {
  text: string;
  startFrame: number;
  charDelayFrames: number;
  fontSize: number;
  fontWeight: number;
  fontStyle?: 'normal' | 'italic';
  color: string;
  centerX: number;
  centerY: number;
}

export const TypewriterText: React.FC<TypewriterTextProps> = ({
  text,
  startFrame,
  charDelayFrames,
  fontSize,
  fontWeight,
  fontStyle = 'normal',
  color,
  centerX,
  centerY,
}) => {
  const frame = useCurrentFrame();
  const elapsed = frame - startFrame;

  if (elapsed < 0) return null;

  const totalChars = text.length;
  const charsVisible = Math.min(
    totalChars,
    Math.floor(elapsed / charDelayFrames)
  );

  // Show cursor blink during typing
  const isTyping = charsVisible < totalChars;
  const cursorVisible = isTyping && Math.floor(elapsed / 4) % 2 === 0;

  const visibleText = text.slice(0, charsVisible);
  const cursorChar = cursorVisible ? '|' : '';

  return (
    <div
      style={{
        position: 'absolute',
        left: centerX,
        top: centerY,
        transform: 'translateX(-50%)',
        fontFamily: 'Inter, sans-serif',
        fontSize,
        fontWeight,
        fontStyle,
        color,
        whiteSpace: 'nowrap',
        lineHeight: '52px',
      }}
    >
      {visibleText}
      <span style={{ opacity: 0.5 }}>{cursorChar}</span>
    </div>
  );
};

export default TypewriterText;
