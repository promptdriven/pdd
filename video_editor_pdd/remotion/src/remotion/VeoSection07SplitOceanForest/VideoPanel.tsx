import React from 'react';
import { useCurrentFrame, interpolate, Easing, OffthreadVideo, staticFile } from 'remotion';
import { CANVAS, DIMENSIONS, ANIMATION } from './constants';

interface VideoPanelProps {
  src: string;
  side: 'left' | 'right';
}

export const VideoPanel: React.FC<VideoPanelProps> = ({ src, side }) => {
  const frame = useCurrentFrame();

  // Both panels start full-width centered, slide apart to reveal split
  // Left panel: slides from center (X offset 0 centered) to X=0
  // Right panel: slides from center to X=972
  const panelX = interpolate(
    frame,
    [ANIMATION.panelSlideStart, ANIMATION.panelSlideEnd],
    side === 'left'
      ? [(CANVAS.width - DIMENSIONS.panelWidth) / 2, 0]
      : [(CANVAS.width - DIMENSIONS.panelWidth) / 2, CANVAS.width - DIMENSIONS.panelWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: panelX,
        top: 0,
        width: DIMENSIONS.panelWidth,
        height: DIMENSIONS.panelHeight,
        overflow: 'hidden',
        zIndex: 1,
      }}
    >
      <OffthreadVideo
        src={staticFile(src)}
        style={{
          width: CANVAS.width,
          height: CANVAS.height,
          objectFit: 'cover',
          // Offset the video so each panel shows its respective half
          marginLeft: side === 'left' ? 0 : -(CANVAS.width - DIMENSIONS.panelWidth),
        }}
      />
    </div>
  );
};
