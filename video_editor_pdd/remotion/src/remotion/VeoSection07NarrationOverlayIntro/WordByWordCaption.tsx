import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, PANEL, DATA, ANIMATION, WAVEFORM } from './constants';

/**
 * Renders all caption words visible from frame 0 in inactive color.
 * The currently-active word highlights gold with a slight scale-up.
 * At frame 60+ all words turn gold before the panel exits.
 */
export const WordByWordCaption: React.FC = () => {
  const frame = useCurrentFrame();

  const { words, wordTimingFrames } = DATA;
  const lastWordStart = wordTimingFrames[wordTimingFrames.length - 1];

  // Left offset to avoid overlapping the waveform visualizer
  const textLeftPad =
    WAVEFORM.x +
    WAVEFORM.barCount * WAVEFORM.barWidth +
    (WAVEFORM.barCount - 1) * WAVEFORM.barGap +
    32;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: textLeftPad,
        right: 80,
        height: PANEL.height,
        display: 'flex',
        alignItems: 'center',
      }}
    >
      <div
        style={{
          display: 'flex',
          flexWrap: 'wrap',
          gap: '0 10px',
        }}
      >
        {words.map((word, i) => {
          const wordStart = wordTimingFrames[i];
          const nextWordStart =
            i < wordTimingFrames.length - 1
              ? wordTimingFrames[i + 1]
              : lastWordStart + 8;

          // Is this word currently the active word?
          const isActive = frame >= wordStart && frame < nextWordStart;

          // After frame 60 all words turn gold
          const isAllGold = frame >= ANIMATION.allGoldStart;

          // Determine color: active or all-gold → gold, else inactive
          const color =
            isActive || isAllGold ? COLORS.activeWord : COLORS.inactiveWord;

          // Scale-up for active word: 1 → 1.05 (easeOutQuad)
          const scale =
            isActive && !isAllGold
              ? interpolate(
                  frame,
                  [wordStart, Math.min(wordStart + 4, nextWordStart)],
                  [1, 1.05],
                  {
                    extrapolateLeft: 'clamp',
                    extrapolateRight: 'clamp',
                    easing: Easing.out(Easing.quad),
                  },
                )
              : 1;

          return (
            <span
              key={i}
              style={{
                fontFamily: TYPOGRAPHY.caption.fontFamily,
                fontSize: TYPOGRAPHY.caption.fontSize,
                fontWeight: TYPOGRAPHY.caption.fontWeight,
                lineHeight: TYPOGRAPHY.caption.lineHeight,
                color,
                display: 'inline-block',
                whiteSpace: 'nowrap',
                transform: `scale(${scale})`,
                transition: 'color 0.05s',
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
