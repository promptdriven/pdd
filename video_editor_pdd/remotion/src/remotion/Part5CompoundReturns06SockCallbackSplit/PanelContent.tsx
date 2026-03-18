import React from 'react';
import { interpolate, useCurrentFrame, Easing, OffthreadVideo } from 'remotion';
import {
  HEIGHT,
  HEADER_FONT_SIZE,
  HEADER_FONT_WEIGHT,
  HEADER_LETTER_SPACING,
  HEADER_Y,
  HEADER_OPACITY,
  HEADER_FADE_START,
  HEADER_FADE_DURATION,
  CAPTION_Y,
  CAPTION_FADE_START,
  CAPTION_FADE_DURATION,
  REALIZATION_FLASH_START,
  FLASH_RAMP_UP,
  FLASH_RAMP_DOWN,
  FLASH_PEAK_OPACITY,
  FLASH_COLOR,
} from './constants';

interface PanelContentProps {
  side: 'left' | 'right';
  panelWidth: number;
  headerText: string;
  headerColor: string;
  gradeColor: string;
  gradeOpacity: number;
  vignetteEdge: string;
  videoSrc: string | null;
  captionNode: React.ReactNode;
  iconNode: React.ReactNode;
}

export const PanelContent: React.FC<PanelContentProps> = ({
  panelWidth,
  headerText,
  headerColor,
  gradeColor,
  gradeOpacity,
  vignetteEdge,
  videoSrc,
  captionNode,
  iconNode,
}) => {
  const frame = useCurrentFrame();

  // Header fade in
  const headerOpacity = interpolate(
    frame,
    [HEADER_FADE_START, HEADER_FADE_START + HEADER_FADE_DURATION],
    [0, HEADER_OPACITY],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Caption fade in
  const captionOpacity = interpolate(
    frame,
    [CAPTION_FADE_START, CAPTION_FADE_START + CAPTION_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Realization flash brightness
  const flashOpacity = interpolate(
    frame,
    [
      REALIZATION_FLASH_START,
      REALIZATION_FLASH_START + FLASH_RAMP_UP,
      REALIZATION_FLASH_START + FLASH_RAMP_UP + FLASH_RAMP_DOWN,
    ],
    [0, FLASH_PEAK_OPACITY, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <div
      style={{
        position: 'relative',
        width: panelWidth,
        height: HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* Veo video background */}
      {videoSrc && (
        <OffthreadVideo
          src={videoSrc}
          style={{
            position: 'absolute',
            top: 0,
            left: 0,
            width: panelWidth,
            height: HEIGHT,
            objectFit: 'cover',
          }}
          muted
        />
      )}

      {/* Fallback gradient background when no video */}
      {!videoSrc && (
        <div
          style={{
            position: 'absolute',
            top: 0,
            left: 0,
            width: panelWidth,
            height: HEIGHT,
            background: `linear-gradient(135deg, ${gradeColor}22 0%, ${vignetteEdge} 100%)`,
          }}
        />
      )}

      {/* Color grade overlay */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: panelWidth,
          height: HEIGHT,
          backgroundColor: gradeColor,
          opacity: gradeOpacity,
        }}
      />

      {/* Vignette overlay — radial gradient darkening edges */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: panelWidth,
          height: HEIGHT,
          background: `radial-gradient(ellipse at center, transparent 40%, ${vignetteEdge} 100%)`,
          opacity: 0.3,
        }}
      />

      {/* Realization flash overlay */}
      {flashOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            top: 0,
            left: 0,
            width: panelWidth,
            height: HEIGHT,
            backgroundColor: FLASH_COLOR,
            opacity: flashOpacity,
          }}
        />
      )}

      {/* Panel header */}
      <div
        style={{
          position: 'absolute',
          top: HEADER_Y,
          left: 0,
          width: panelWidth,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: HEADER_FONT_SIZE,
          fontWeight: HEADER_FONT_WEIGHT,
          letterSpacing: HEADER_LETTER_SPACING,
          color: headerColor,
          opacity: headerOpacity,
        }}
      >
        {headerText}
      </div>

      {/* Caption area */}
      <div
        style={{
          position: 'absolute',
          top: CAPTION_Y,
          left: 0,
          width: panelWidth,
          textAlign: 'center',
          opacity: captionOpacity,
        }}
      >
        {captionNode}
      </div>

      {/* Icon area */}
      {iconNode}
    </div>
  );
};
