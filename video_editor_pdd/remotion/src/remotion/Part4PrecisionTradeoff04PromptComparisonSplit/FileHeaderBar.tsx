import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, FILE_HEADER_HEIGHT } from './constants';

interface FileHeaderBarProps {
  filename: string;
  panelX: number;
  panelWidth: number;
  y: number;
  /** Frame at which to start appearing */
  startFrame?: number;
}

export const FileHeaderBar: React.FC<FileHeaderBarProps> = ({
  filename,
  panelX,
  panelWidth,
  y,
  startFrame = 20,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [startFrame, startFrame + 10],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: panelX,
        top: y,
        width: panelWidth,
        height: FILE_HEADER_HEIGHT,
        backgroundColor: COLORS.fileHeaderBg,
        display: 'flex',
        alignItems: 'center',
        paddingLeft: 12,
        opacity,
      }}
    >
      <span
        style={{
          fontFamily: '"JetBrains Mono", monospace',
          fontSize: 11,
          color: COLORS.fileNameColor,
          opacity: 0.7,
        }}
      >
        {filename}
      </span>
    </div>
  );
};
