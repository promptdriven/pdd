import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import {
  COLORS,
  TYPOGRAPHY,
  DIMENSIONS,
  POSITIONS,
  ANIMATION_TIMING,
  NARRATION_TEXT,
  TYPE_SPEED,
} from './constants';

export const TypeOnText: React.FC = () => {
  const frame = useCurrentFrame();

  const elapsedFrames = Math.max(0, frame - ANIMATION_TIMING.typeOnStart);
  const charCount = Math.min(
    Math.floor(elapsedFrames * TYPE_SPEED),
    NARRATION_TEXT.length
  );

  const visibleText = NARRATION_TEXT.slice(0, charCount);

  // Blinking cursor while typing
  const isTyping = charCount < NARRATION_TEXT.length && frame >= ANIMATION_TIMING.typeOnStart;
  const cursorOpacity = isTyping
    ? interpolate(Math.sin(frame * 0.3), [-1, 1], [0.3, 1])
    : 0;

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.textY,
        left: '50%',
        transform: 'translateX(-50%)',
        maxWidth: DIMENSIONS.textMaxWidth,
        padding: DIMENSIONS.textPadding,
        textAlign: 'left',
      }}
    >
      <span
        style={{
          fontFamily: TYPOGRAPHY.subtitle.fontFamily,
          fontSize: TYPOGRAPHY.subtitle.fontSize,
          fontWeight: TYPOGRAPHY.subtitle.fontWeight,
          letterSpacing: TYPOGRAPHY.subtitle.letterSpacing,
          color: COLORS.text,
          textShadow: '0 2px 8px rgba(0,0,0,0.6)',
          lineHeight: 1.4,
        }}
      >
        {visibleText}
      </span>
      <span
        style={{
          display: 'inline-block',
          width: 2,
          height: TYPOGRAPHY.subtitle.fontSize,
          backgroundColor: COLORS.text,
          marginLeft: 2,
          opacity: cursorOpacity,
          verticalAlign: 'text-bottom',
        }}
      />
    </div>
  );
};
