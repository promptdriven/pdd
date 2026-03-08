import React from 'react';
import { useCurrentFrame } from 'remotion';
import { COLORS, TYPOGRAPHY, POSITIONS, DIMENSIONS, ANIMATION, NARRATION_TEXT } from './constants';

export const TypeOnSubtitle: React.FC = () => {
  const frame = useCurrentFrame();

  const typeFrame = Math.max(0, frame - ANIMATION.subtitleTypeStart);
  const charsVisible = Math.min(
    Math.floor(typeFrame * ANIMATION.charsPerFrame),
    NARRATION_TEXT.length,
  );

  if (frame < ANIMATION.subtitleTypeStart) return null;

  const visibleText = NARRATION_TEXT.slice(0, charsVisible);
  const isTyping = charsVisible < NARRATION_TEXT.length;

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.subtitleX,
        top: POSITIONS.subtitleY,
        maxWidth: DIMENSIONS.subtitleMaxWidth,
      }}
    >
      <span
        style={{
          color: COLORS.subtitleText,
          fontSize: TYPOGRAPHY.subtitle.fontSize,
          fontFamily: TYPOGRAPHY.subtitle.fontFamily,
          fontWeight: TYPOGRAPHY.subtitle.fontWeight,
          letterSpacing: TYPOGRAPHY.subtitle.letterSpacing,
          lineHeight: TYPOGRAPHY.subtitle.lineHeight,
          textShadow: '0 2px 8px rgba(0,0,0,0.6)',
        }}
      >
        {visibleText}
        {isTyping && (
          <span
            style={{
              display: 'inline-block',
              width: 2,
              height: TYPOGRAPHY.subtitle.fontSize,
              backgroundColor: COLORS.badgeText,
              marginLeft: 2,
              verticalAlign: 'text-bottom',
              opacity: Math.round(frame * 0.12) % 2 === 0 ? 1 : 0,
            }}
          />
        )}
      </span>
    </div>
  );
};
