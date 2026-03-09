import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, TYPOGRAPHY, POSITIONS, ANIMATION, COLORS } from './constants';

/**
 * "NARRATION AUDIO" label centered above the waveform.
 * Fades in during phase 1, fades out during phase 3.
 */
export const SectionLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [
      ANIMATION.growStart,
      ANIMATION.labelFadeInEnd,
      ANIMATION.labelFadeOutStart,
      ANIMATION.shrinkEnd,
    ],
    [0, 0.5, 0.5, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.labelY,
        left: 0,
        width: CANVAS.width,
        textAlign: 'center',
        fontFamily: TYPOGRAPHY.sectionLabel.fontFamily,
        fontWeight: TYPOGRAPHY.sectionLabel.fontWeight,
        fontSize: TYPOGRAPHY.sectionLabel.fontSize,
        letterSpacing: TYPOGRAPHY.sectionLabel.letterSpacing,
        color: COLORS.labelText,
        textTransform: 'uppercase',
        opacity,
      }}
    >
      NARRATION AUDIO
    </div>
  );
};
