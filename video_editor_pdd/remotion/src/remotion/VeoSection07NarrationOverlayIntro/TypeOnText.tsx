import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { ANIMATION, type NarrationOverlayLayout } from './constants';

export const TypeOnText: React.FC<{ text: string; layout: NarrationOverlayLayout }> = ({
  text,
  layout,
}) => {
  const frame = useCurrentFrame();

  // Characters revealed linearly between typeOnStart and typeOnEnd
  const totalChars = text.length;
  const charsVisible = Math.floor(
    interpolate(
      frame,
      [ANIMATION.typeOnStart, ANIMATION.typeOnEnd],
      [0, totalChars],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      },
    ),
  );

  const visibleText = text.slice(0, charsVisible);

  return (
    <div
      style={{
        position: 'absolute',
        top: layout.pill.textPaddingY,
        left: layout.pill.textPaddingX,
        maxWidth: layout.pill.textMaxWidth,
        fontFamily: layout.typography.narration.fontFamily,
        fontSize: layout.typography.narration.fontSize,
        fontWeight: layout.typography.narration.fontWeight,
        lineHeight: layout.typography.narration.lineHeight,
        color: '#FFFFFF',
        whiteSpace: 'pre-wrap',
        wordBreak: 'break-word',
      }}
    >
      {visibleText}
      {charsVisible < totalChars && (
        <span
          style={{
            display: 'inline-block',
            width: 2,
            height: layout.typography.narration.fontSize,
            backgroundColor: '#FFFFFF',
            marginLeft: 1,
            opacity: frame % 10 < 5 ? 1 : 0.3,
            verticalAlign: 'text-bottom',
          }}
        />
      )}
    </div>
  );
};
