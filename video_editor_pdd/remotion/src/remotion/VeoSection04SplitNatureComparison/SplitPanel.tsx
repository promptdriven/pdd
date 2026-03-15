import React from 'react';
import {
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  DIMENSIONS,
  ANIMATION,
  type SplitComparisonLayout,
} from './constants';

interface SplitPanelProps {
  side: 'left' | 'right';
  videoSrc: string;
  layout: SplitComparisonLayout;
}

export const SplitPanel: React.FC<SplitPanelProps> = ({ side, videoSrc, layout }) => {
  const frame = useCurrentFrame();
  const isLeft = side === 'left';

  const panelX = isLeft ? DIMENSIONS.leftPanelX : DIMENSIONS.rightPanelX;
  const panelWidth = isLeft ? DIMENSIONS.leftPanelWidth : DIMENSIONS.rightPanelWidth;

  // Frame 0–8: split wipe from center outward
  // Left panel: clipPath reveals from right edge to left
  // Right panel: clipPath reveals from left edge to right
  const wipeProgress = interpolate(
    frame,
    [ANIMATION.wipeStart, ANIMATION.wipeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Use clipPath to reveal from center outward
  const clipPath = isLeft
    ? `inset(0 0 0 ${(1 - wipeProgress) * 100}%)`
    : `inset(0 ${(1 - wipeProgress) * 100}% 0 0)`;

  return (
    <div
      style={{
        position: 'absolute',
        left: panelX * layout.scaleX,
        top: 0,
        width: panelWidth * layout.scaleX,
        height: DIMENSIONS.panelHeight * layout.scaleY,
        overflow: 'hidden',
        clipPath,
      }}
    >
      <OffthreadVideo
        src={staticFile(videoSrc)}
        style={{
          position: 'absolute',
          top: '50%',
          left: '50%',
          transform: 'translate(-50%, -50%)',
          minWidth: '100%',
          minHeight: '100%',
          objectFit: 'cover',
        }}
        muted
      />
    </div>
  );
};
