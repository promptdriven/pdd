import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, PANEL, DATA } from './constants';

export const TypewriterCaption: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        padding: PANEL.padding,
        boxSizing: 'border-box',
      }}
    >
      <div
        style={{
          display: 'flex',
          flexWrap: 'wrap',
          justifyContent: 'center',
          gap: '0 10px',
        }}
      >
        {DATA.words.map((word, i) => {
          const wordStart = DATA.wordTimingFrames[i];
          const wordEnd = wordStart + DATA.wordFadeDuration;

          // Opacity: 0→1 over wordFadeDuration frames
          const opacity = interpolate(frame, [wordStart, wordEnd], [0, 1], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });

          // Brief gold highlight that fades to white
          const highlightProgress = interpolate(
            frame,
            [wordStart, wordEnd + 4],
            [0, 1],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
            },
          );

          // Blend from gold (#C9A84C) to white (#FFFFFF)
          const color =
            highlightProgress < 1 ? COLORS.wordHighlight : COLORS.captionText;

          return (
            <span
              key={i}
              style={{
                fontFamily: TYPOGRAPHY.caption.fontFamily,
                fontSize: TYPOGRAPHY.caption.fontSize,
                fontWeight: TYPOGRAPHY.caption.fontWeight,
                lineHeight: TYPOGRAPHY.caption.lineHeight,
                color,
                opacity,
                display: 'inline-block',
                whiteSpace: 'nowrap',
              }}
            >
              {word}
            </span>
          );
        })}
      </div>
    </div>
  );
};
