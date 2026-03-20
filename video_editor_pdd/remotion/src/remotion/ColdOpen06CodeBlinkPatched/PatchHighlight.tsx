import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CODE_X_START,
  CODE_Y_START,
  CODE_LINE_HEIGHT,
  CODE_X_END,
  HIGHLIGHTS_START_FRAME,
  HIGHLIGHT_STAGGER_FRAMES,
  HIGHLIGHT_FADE_DURATION,
  PATCH_SCARS,
} from './constants';

/**
 * Renders the patch scar highlights — colored background strips behind
 * specific comment lines that fade in sequentially.
 */
export const PatchHighlights: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <>
      {PATCH_SCARS.map((scar, idx) => {
        const startFrame =
          HIGHLIGHTS_START_FRAME + idx * HIGHLIGHT_STAGGER_FRAMES;
        const endFrame = startFrame + HIGHLIGHT_FADE_DURATION;

        const opacity = interpolate(
          frame,
          [startFrame, endFrame],
          [0, scar.targetOpacity],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          },
        );

        const y = CODE_Y_START + scar.lineIndex * CODE_LINE_HEIGHT;

        return (
          <div
            key={idx}
            style={{
              position: 'absolute',
              left: CODE_X_START - 8,
              top: y,
              width: CODE_X_END - CODE_X_START + 16,
              height: CODE_LINE_HEIGHT,
              backgroundColor: scar.highlightColor,
              opacity,
              borderRadius: 2,
              pointerEvents: 'none',
            }}
          />
        );
      })}
    </>
  );
};
