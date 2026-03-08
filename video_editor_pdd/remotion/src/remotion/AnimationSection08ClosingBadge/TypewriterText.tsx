import React from 'react';
import { useCurrentFrame } from 'remotion';
import { COLORS, POSITIONS, TYPOGRAPHY, ANIMATION_TIMING } from './constants';

const BRAND_NAME = 'Remotion';

export const TypewriterText: React.FC = () => {
  const frame = useCurrentFrame();

  const elapsed = frame - ANIMATION_TIMING.typewriterStart;
  const visibleChars = Math.min(
    Math.max(0, Math.floor(elapsed / ANIMATION_TIMING.charInterval)),
    BRAND_NAME.length
  );

  const displayText = BRAND_NAME.slice(0, visibleChars);

  // Cursor blink — visible when still typing
  const showCursor =
    visibleChars < BRAND_NAME.length && frame >= ANIMATION_TIMING.typewriterStart;

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.textCenterY,
        left: 0,
        right: 0,
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      <span
        style={{
          fontFamily: TYPOGRAPHY.brandName.fontFamily,
          fontSize: TYPOGRAPHY.brandName.fontSize,
          fontWeight: TYPOGRAPHY.brandName.fontWeight,
          letterSpacing: TYPOGRAPHY.brandName.letterSpacing,
          color: COLORS.textColor,
          whiteSpace: 'pre',
        }}
      >
        {displayText}
        {showCursor && (
          <span
            style={{
              color: COLORS.gradientStart,
              fontWeight: 300,
            }}
          >
            |
          </span>
        )}
      </span>
    </div>
  );
};
