import React from 'react';
import { OffthreadVideo, staticFile } from 'remotion';
import {
  DIMENSIONS,
  type SplitNatureComparisonLayout,
} from './constants';

interface SplitPanelProps {
  side: 'left' | 'right';
  videoSrc: string;
  layout: SplitNatureComparisonLayout;
}

export const SplitPanel: React.FC<SplitPanelProps> = ({ side, videoSrc, layout }) => {
  const isLeft = side === 'left';
  const panelX = isLeft ? DIMENSIONS.leftPanelX : DIMENSIONS.rightPanelX;
  const panelY = isLeft ? DIMENSIONS.leftPanelY : DIMENSIONS.rightPanelY;

  return (
    <div
      style={{
        position: 'absolute',
        left: panelX * layout.scaleX,
        top: panelY * layout.scaleY,
        width: DIMENSIONS.panelWidth * layout.scaleX,
        height: DIMENSIONS.panelHeight * layout.scaleY,
        borderRadius: DIMENSIONS.panelBorderRadius * layout.uniformScale,
        overflow: 'hidden',
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
