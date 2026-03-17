import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, MONO_FONT, FILE_HEADER_HEIGHT } from './constants';

const FileHeader: React.FC<{
  filename: string;
  x: number;
  y: number;
  width: number;
  appearFrame: number;
}> = ({ filename, x, y, width, appearFrame }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [appearFrame, appearFrame + 10], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
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
          fontFamily: MONO_FONT,
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

export default FileHeader;
