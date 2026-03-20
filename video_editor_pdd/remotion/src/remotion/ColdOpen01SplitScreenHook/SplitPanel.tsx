import React from 'react';
import { OffthreadVideo } from 'remotion';
import { FilmGrain } from './FilmGrain';
import {
  COMP_HEIGHT,
  HEADER_FONT_FAMILY,
  HEADER_FONT_SIZE,
  HEADER_FONT_WEIGHT,
  HEADER_TEXT_COLOR,
  HEADER_TEXT_OPACITY,
} from './constants';

interface SplitPanelProps {
  /** Panel width in pixels */
  width: number;
  /** Video source path (already resolved — do NOT wrap in staticFile) */
  videoSrc: string;
  /** Color tint overlay */
  tintColor: string;
  tintOpacity: number;
  /** Vignette */
  vignetteColor: string;
  vignetteOpacity: number;
  /** Year label */
  label: string;
  labelX: number;
  labelY: number;
  /** Optional film grain */
  showFilmGrain?: boolean;
  filmGrainOpacity?: number;
  filmGrainFps?: number;
}

export const SplitPanel: React.FC<SplitPanelProps> = ({
  width,
  videoSrc,
  tintColor,
  tintOpacity,
  vignetteColor,
  vignetteOpacity,
  label,
  labelX,
  labelY,
  showFilmGrain = false,
  filmGrainOpacity = 0.06,
  filmGrainFps = 12,
}) => {
  const height = COMP_HEIGHT;

  return (
    <div
      style={{
        position: 'relative',
        width,
        height,
        overflow: 'hidden',
      }}
    >
      {/* Video layer */}
      <OffthreadVideo
        src={videoSrc}
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width,
          height,
          objectFit: 'cover',
        }}
        muted
      />

      {/* Color grading tint overlay */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width,
          height,
          backgroundColor: tintColor,
          opacity: tintOpacity,
          pointerEvents: 'none',
        }}
      />

      {/* Vignette overlay */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width,
          height,
          background: `radial-gradient(ellipse at center, transparent 40%, ${vignetteColor} 100%)`,
          opacity: vignetteOpacity,
          pointerEvents: 'none',
        }}
      />

      {/* Film grain (right panel only) */}
      {showFilmGrain && (
        <FilmGrain
          width={width}
          height={height}
          opacity={filmGrainOpacity}
          fps={filmGrainFps}
        />
      )}

      {/* Panel header label */}
      <div
        style={{
          position: 'absolute',
          top: labelY,
          left: labelX,
          fontFamily: HEADER_FONT_FAMILY,
          fontSize: HEADER_FONT_SIZE,
          fontWeight: HEADER_FONT_WEIGHT,
          color: HEADER_TEXT_COLOR,
          opacity: HEADER_TEXT_OPACITY,
          letterSpacing: '0.05em',
          userSelect: 'none',
          zIndex: 20,
          textShadow: '0 0 8px rgba(0,0,0,0.9), 0 0 2px rgba(0,0,0,0.7)',
        }}
      >
        {label}
      </div>
    </div>
  );
};

export default SplitPanel;
