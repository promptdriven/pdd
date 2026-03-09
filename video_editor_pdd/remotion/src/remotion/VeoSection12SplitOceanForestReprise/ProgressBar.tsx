import React from 'react';
import { CANVAS, COLORS, PROGRESS_BAR } from './constants';

interface ProgressBarProps {
  progress: number; // 0 to 1
}

export const ProgressBar: React.FC<ProgressBarProps> = ({ progress }) => {
  const barWidth = CANVAS.width * progress;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: PROGRESS_BAR.y,
        width: CANVAS.width,
        height: PROGRESS_BAR.height,
        zIndex: 10,
      }}
    >
      <div
        style={{
          width: barWidth,
          height: PROGRESS_BAR.height,
          background: `linear-gradient(to right, ${COLORS.progressStart}, ${COLORS.progressEnd})`,
          borderRadius: 2,
        }}
      />
    </div>
  );
};
