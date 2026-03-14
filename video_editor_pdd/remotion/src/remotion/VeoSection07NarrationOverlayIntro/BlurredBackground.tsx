import React from 'react';
import {
  useCurrentFrame,
  interpolate,
  Easing,
  Img,
  OffthreadVideo,
  staticFile,
} from 'remotion';
import { useVisualMediaSrc } from '../_shared/visual-runtime';
import { COLORS, ANIMATION, DIMENSIONS } from './constants';

export const BlurredBackground: React.FC = () => {
  const frame = useCurrentFrame();
  const backgroundSrc = useVisualMediaSrc('backgroundSrc');
  const backgroundExtension = backgroundSrc?.split('.').pop()?.toLowerCase() ?? null;
  const isImageBackground =
    backgroundExtension === 'png' ||
    backgroundExtension === 'jpg' ||
    backgroundExtension === 'jpeg' ||
    backgroundExtension === 'webp';

  // Frame 0–4: Fade in opacity 0→1, easeOutCubic
  const opacity = interpolate(
    frame,
    [ANIMATION.bgFadeStart, ANIMATION.bgFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        opacity,
      }}
    >
      {/* Blurred Veo footage still or solid fallback */}
      {backgroundSrc ? (
        isImageBackground ? (
          <Img
            src={staticFile(backgroundSrc)}
            style={{
              position: 'absolute',
              top: 0,
              left: 0,
              width: '100%',
              height: '100%',
              objectFit: 'cover',
              filter: `blur(${DIMENSIONS.backgroundBlur}px)`,
              // Scale up slightly to prevent blur edge artifacts
              transform: 'scale(1.05)',
            }}
          />
        ) : (
          <OffthreadVideo
            src={staticFile(backgroundSrc)}
            style={{
              position: 'absolute',
              top: 0,
              left: 0,
              width: '100%',
              height: '100%',
              objectFit: 'cover',
              filter: `blur(${DIMENSIONS.backgroundBlur}px)`,
              transform: 'scale(1.05)',
            }}
          />
        )
      ) : (
        <div
          style={{
            position: 'absolute',
            top: 0,
            left: 0,
            width: '100%',
            height: '100%',
            backgroundColor: COLORS.background,
          }}
        />
      )}

      {/* Dark overlay at 50% opacity */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
          backgroundColor: COLORS.overlay,
        }}
      />
    </div>
  );
};
