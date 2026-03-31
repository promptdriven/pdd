import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';

interface TypewriterTextProps {
  text: string;
  startFrame: number;
  /** Number of frames to type the full text */
  typingFrames: number;
  color: string;
  fontSize: number;
  fontFamily: string;
  prefix?: string;
  prefixColor?: string;
}

/**
 * Typewriter effect that reveals text character by character.
 */
export const TypewriterText: React.FC<TypewriterTextProps> = ({
  text,
  startFrame,
  typingFrames,
  color,
  fontSize,
  fontFamily,
  prefix = '$ ',
  prefixColor,
}) => {
  const frame = useCurrentFrame();
  const relativeFrame = frame - startFrame;

  if (relativeFrame < 0) return null;

  const charCount = Math.floor(
    interpolate(relativeFrame, [0, typingFrames], [0, text.length], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    })
  );

  const displayedText = text.slice(0, charCount);
  const showCursor = relativeFrame < typingFrames + 15;
  const cursorBlink = Math.floor(relativeFrame / 8) % 2 === 0;

  return (
    <div
      style={{
        fontFamily,
        fontSize,
        lineHeight: 1.7,
        whiteSpace: 'pre',
      }}
    >
      {prefix && (
        <span style={{ color: prefixColor || color, opacity: 0.7 }}>
          {prefix}
        </span>
      )}
      <span style={{ color }}>{displayedText}</span>
      {showCursor && (
        <span
          style={{
            color,
            opacity: cursorBlink ? 1 : 0,
          }}
        >
          _
        </span>
      )}
    </div>
  );
};

export default TypewriterText;
