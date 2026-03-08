import React from 'react';
import { interpolate, useCurrentFrame } from 'remotion';
import { COLORS, TYPOGRAPHY, LAYOUT, ANIMATION } from './constants';

interface TypewriterTextProps {
  text: string;
}

export const TypewriterText: React.FC<TypewriterTextProps> = ({ text }) => {
  const frame = useCurrentFrame();

  // Calculate how many characters to show
  const charsToShow = Math.min(
    Math.floor(frame / ANIMATION.typewriter.framesPerChar),
    text.length
  );

  const visibleText = text.slice(0, charsToShow);
  const isTypingComplete = charsToShow >= text.length;

  // Cursor blink logic
  const totalFrames = ANIMATION.typewriter.endFrame;
  const shouldShowCursor = isTypingComplete
    ? Math.floor((frame - (text.length * ANIMATION.typewriter.framesPerChar)) / ANIMATION.typewriter.blinkInterval) % 2 === 0
    : Math.floor(frame / ANIMATION.typewriter.blinkInterval) % 2 === 0;

  const showCursor = frame <= totalFrames && shouldShowCursor;

  return (
    <div
      style={{
        position: 'absolute',
        top: LAYOUT.headline.y,
        left: LAYOUT.headline.x,
        transform: 'translate(-50%, -50%)',
        display: 'flex',
        alignItems: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: TYPOGRAPHY.headline.fontSize,
        fontWeight: TYPOGRAPHY.headline.fontWeight,
        letterSpacing: TYPOGRAPHY.headline.letterSpacing,
        color: COLORS.headline,
        whiteSpace: 'nowrap',
      }}
    >
      <span>{visibleText}</span>
      {showCursor && (
        <div
          style={{
            width: LAYOUT.cursor.width,
            height: LAYOUT.cursor.height,
            backgroundColor: COLORS.cursor,
            marginLeft: 4,
          }}
        />
      )}
    </div>
  );
};
