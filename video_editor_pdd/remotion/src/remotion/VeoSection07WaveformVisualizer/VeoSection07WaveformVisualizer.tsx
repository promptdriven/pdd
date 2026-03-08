import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, POSITIONS, DIMENSIONS, ANIMATION } from './constants';
import { WaveformBars } from './WaveformBars';
import { Playhead } from './Playhead';
import { NarrationLabel } from './NarrationLabel';
import { TimestampCounter } from './TimestampCounter';

export const VeoSection07WaveformVisualizer: React.FC = () => {
  const frame = useCurrentFrame();

  // Backdrop fade in, then fade out
  const backdropOpacity = interpolate(
    frame,
    [
      ANIMATION.backdropFadeStart, ANIMATION.backdropFadeEnd,
      ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd,
    ],
    [0, 1, 1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Backdrop panel */}
      <div
        style={{
          position: 'absolute',
          left: POSITIONS.containerCenterX - DIMENSIONS.backdropWidth / 2,
          top: POSITIONS.containerCenterY - DIMENSIONS.backdropHeight / 2,
          width: DIMENSIONS.backdropWidth,
          height: DIMENSIONS.backdropHeight,
          backgroundColor: COLORS.backdropBg,
          borderRadius: DIMENSIONS.backdropBorderRadius,
          border: `1px solid ${COLORS.backdropBorder}`,
          opacity: backdropOpacity,
        }}
      >
        {/* Waveform bars inside the backdrop */}
        <WaveformBars />
        {/* Playhead sweeping across */}
        <Playhead />
      </div>

      {/* Label: NARRATION SYNC */}
      <NarrationLabel />

      {/* Timestamp counter */}
      <TimestampCounter />
    </AbsoluteFill>
  );
};

export const defaultVeoSection07WaveformVisualizerProps = {};

export default VeoSection07WaveformVisualizer;
