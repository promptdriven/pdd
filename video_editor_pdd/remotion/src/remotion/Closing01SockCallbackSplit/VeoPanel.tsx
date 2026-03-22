import React from 'react';
import { OffthreadVideo } from 'remotion';

interface VeoPanelProps {
  src: string | null;
  panelX: number;
  panelWidth: number;
  gradeColor: string;
  gradeOpacity: number;
  vignetteColor: string;
}

export const VeoPanel: React.FC<VeoPanelProps> = ({
  src,
  panelX,
  panelWidth,
  gradeColor,
  gradeOpacity,
  vignetteColor,
}) => {
  return (
    <div
      style={{
        position: 'absolute',
        left: panelX,
        top: 0,
        width: panelWidth,
        height: 1080,
        overflow: 'hidden',
      }}
    >
      {/* Video or placeholder */}
      {src ? (
        <OffthreadVideo
          src={src}
          style={{
            position: 'absolute',
            left: 0,
            top: 0,
            width: panelWidth,
            height: 1080,
            objectFit: 'cover',
          }}
          muted
        />
      ) : (
        <div
          style={{
            position: 'absolute',
            left: 0,
            top: 0,
            width: panelWidth,
            height: 1080,
            background: `linear-gradient(135deg, ${gradeColor}22 0%, #111 100%)`,
          }}
        />
      )}

      {/* Color grade overlay */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: panelWidth,
          height: 1080,
          backgroundColor: gradeColor,
          opacity: gradeOpacity,
          pointerEvents: 'none',
        }}
      />

      {/* Vignette overlay */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: panelWidth,
          height: 1080,
          background: `radial-gradient(ellipse at center, transparent 40%, ${vignetteColor} 100%)`,
          opacity: 0.25,
          pointerEvents: 'none',
        }}
      />

      {/* Top gradient strip — contrast for panel headers */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: panelWidth,
          height: 90,
          background: 'linear-gradient(to bottom, rgba(0,0,0,0.7) 0%, transparent 100%)',
          pointerEvents: 'none',
        }}
      />

      {/* Bottom gradient strip — contrast for cost labels and sub-labels */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          bottom: 0,
          width: panelWidth,
          height: 180,
          background: 'linear-gradient(to top, rgba(0,0,0,0.7) 0%, transparent 100%)',
          pointerEvents: 'none',
        }}
      />
    </div>
  );
};
