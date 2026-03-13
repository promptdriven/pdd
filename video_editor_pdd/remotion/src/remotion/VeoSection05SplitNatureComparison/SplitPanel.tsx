import React from 'react';
import { OffthreadVideo, staticFile } from 'remotion';
import {
  COLORS,
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

  return (
    <div
      style={{
        position: 'absolute',
        left: panelX * layout.scaleX,
        top: DIMENSIONS.leftPanelY * layout.scaleY,
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

      {/* Subtle vignette on divider edge */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          [isLeft ? 'right' : 'left']: 0,
          width: 20 * layout.uniformScale,
          height: '100%',
          background: isLeft
            ? `linear-gradient(to left, ${COLORS.vignette}, transparent)`
            : `linear-gradient(to right, ${COLORS.vignette}, transparent)`,
          pointerEvents: 'none',
        }}
      />
    </div>
  );
};
