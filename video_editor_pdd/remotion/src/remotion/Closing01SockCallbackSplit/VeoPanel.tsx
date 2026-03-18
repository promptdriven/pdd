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
    </div>
  );
};
