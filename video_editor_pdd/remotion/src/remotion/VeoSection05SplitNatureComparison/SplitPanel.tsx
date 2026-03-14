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
  type SplitNatureComparisonLayout,
} from './constants';

interface SplitPanelProps {
  side: 'left' | 'right';
  videoSrc: string;
  layout: SplitNatureComparisonLayout;
}

export const SplitPanel: React.FC<SplitPanelProps> = ({ side, videoSrc, layout }) => {
  const frame = useCurrentFrame();
  const isLeft = side === 'left';
  const panelX = isLeft ? DIMENSIONS.leftPanelX : DIMENSIONS.rightPanelX;

  // Frame 0–8: scale from 1.1→1.0 (subtle zoom-out settle), easeOutQuad
  const scale = interpolate(
    frame,
    [ANIMATION.panelZoomStart, ANIMATION.panelZoomEnd],
    [ANIMATION.panelScaleFrom, ANIMATION.panelScaleTo],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: panelX * layout.scaleX,
        top: 0,
        width: DIMENSIONS.panelWidth * layout.scaleX,
        height: DIMENSIONS.panelHeight * layout.scaleY,
        overflow: 'hidden',
      }}
    >
      <OffthreadVideo
        src={staticFile(videoSrc)}
        style={{
          position: 'absolute',
          top: '50%',
          left: '50%',
          transform: `translate(-50%, -50%) scale(${scale})`,
          minWidth: '100%',
          minHeight: '100%',
          objectFit: 'cover',
        }}
        muted
      />
    </div>
  );
};
