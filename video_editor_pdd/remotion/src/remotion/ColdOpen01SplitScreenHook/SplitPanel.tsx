import React from 'react';
import { AbsoluteFill, OffthreadVideo } from 'remotion';

interface SplitPanelProps {
  x: number;
  width: number;
  videoSrc: string | null;
  colorGrade: string;
  colorGradeOpacity: number;
  vignetteEdge: string;
  vignetteOpacity: number;
}

export const SplitPanel: React.FC<SplitPanelProps> = ({
  x,
  width,
  videoSrc,
  colorGrade,
  colorGradeOpacity,
  vignetteEdge,
  vignetteOpacity,
}) => {
  return (
    <AbsoluteFill
      style={{
        left: x,
        width,
        height: '100%',
        overflow: 'hidden',
        position: 'absolute',
        top: 0,
      }}
    >
      {/* Video clip */}
      {videoSrc && (
        <OffthreadVideo
          src={videoSrc}
          style={{
            width: '100%',
            height: '100%',
            objectFit: 'cover',
          }}
          muted
        />
      )}

      {/* Fallback background if no video */}
      {!videoSrc && (
        <AbsoluteFill
          style={{
            backgroundColor: '#111',
          }}
        />
      )}

      {/* Color grade overlay */}
      <AbsoluteFill
        style={{
          backgroundColor: colorGrade,
          opacity: colorGradeOpacity,
        }}
      />

      {/* Vignette overlay */}
      <AbsoluteFill
        style={{
          background: `radial-gradient(ellipse at center, transparent 40%, ${vignetteEdge} 100%)`,
          opacity: vignetteOpacity,
        }}
      />
    </AbsoluteFill>
  );
};
