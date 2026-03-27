import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  RATIO_TEXT_COLOR,
  PROMPT_COLOR,
  RATIO_ANIM_DURATION,
} from './constants';

export const RatioLabel: React.FC<{ startFrame: number }> = ({
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  const opacity = interpolate(localFrame, [0, RATIO_ANIM_DURATION], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const scale = interpolate(
    localFrame,
    [0, RATIO_ANIM_DURATION],
    [0.8, 1.0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 200,
        right: 0,
        top: 560,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        opacity,
        transform: `scale(${scale})`,
      }}
    >
      {/* Connector line */}
      <div
        style={{
          position: 'absolute',
          top: 24,
          left: 350,
          width: 520,
          height: 2,
          backgroundColor: PROMPT_COLOR,
          opacity: 0.2,
        }}
      />

      {/* Ratio text */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 36,
          fontWeight: 700,
          color: RATIO_TEXT_COLOR,
          textAlign: 'center',
          position: 'relative',
          backgroundColor: '#0A0F1A',
          padding: '4px 24px',
          zIndex: 1,
        }}
      >
        1:5 to 1:10
      </div>

      {/* Subtitle */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 13,
          color: '#94A3B8',
          marginTop: 8,
          textAlign: 'center',
        }}
      >
        compression ratio
      </div>
    </div>
  );
};
