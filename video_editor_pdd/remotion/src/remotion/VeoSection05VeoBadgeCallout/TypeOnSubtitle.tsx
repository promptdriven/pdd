import React from 'react';
import { useCurrentFrame } from 'remotion';
import { COLORS, TYPOGRAPHY, POSITIONS, DIMENSIONS, ANIMATION, NARRATION_TEXT } from './constants';

export const TypeOnSubtitle: React.FC = () => {
  const frame = useCurrentFrame();

  // Type-on starts at frame 15
  const typeFrame = Math.max(0, frame - ANIMATION.subtitleTypeStart);
  const charsVisible = Math.min(
    Math.floor(typeFrame * ANIMATION.charsPerFrame),
    NARRATION_TEXT.length,
  );

  if (frame < ANIMATION.subtitleTypeStart) return null;

  const visibleText = NARRATION_TEXT.slice(0, charsVisible);

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
          textShadow: '0 2px 6px rgba(0,0,0,0.5)',
          lineHeight: 1.4,
        }}
      >
        {visibleText}
        {charsVisible < NARRATION_TEXT.length && (
          <span
            style={{
              display: 'inline-block',
              width: 2,
              height: TYPOGRAPHY.subtitle.fontSize,
              backgroundColor: COLORS.subtitleText,
              marginLeft: 2,
              verticalAlign: 'text-bottom',
              opacity: Math.round(frame * 0.15) % 2 === 0 ? 1 : 0,
            }}
          />
        )}
      </span>
    </div>
  );
};
