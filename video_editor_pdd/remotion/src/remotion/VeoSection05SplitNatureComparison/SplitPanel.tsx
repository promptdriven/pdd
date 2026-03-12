import React from 'react';
import { useCurrentFrame, interpolate, Easing, OffthreadVideo, staticFile } from 'remotion';
import { CANVAS, ANIMATION, DIMENSIONS, COLORS } from './constants';

interface SplitPanelProps {
  side: 'left' | 'right';
  videoSrc: string;
}

export const SplitPanel: React.FC<SplitPanelProps> = ({ side, videoSrc }) => {
  const frame = useCurrentFrame();

  const isLeft = side === 'left';
  const wipeStart = isLeft ? ANIMATION.leftPanelWipeStart : ANIMATION.rightPanelWipeStart;
  const wipeEnd = isLeft ? ANIMATION.leftPanelWipeEnd : ANIMATION.rightPanelWipeEnd;

  // Panel width: left=0..957 (957px), right=963..1920 (957px)
  const panelWidth = isLeft ? DIMENSIONS.leftPanelEnd + 1 : CANVAS.width - DIMENSIONS.rightPanelStart;
  const panelLeft = isLeft ? 0 : DIMENSIONS.rightPanelStart;

  // Clip-path reveal: wipe from the divider edge outward
  // For left panel: reveal from right edge toward left
  // For right panel: reveal from left edge toward right
  const revealProgress = interpolate(
    frame,
    [wipeStart, wipeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Ken Burns slow zoom (linear, continuous)
  const zoom = interpolate(
    frame,
    [0, ANIMATION.totalDuration],
    [DIMENSIONS.kenBurnsStart, DIMENSIONS.kenBurnsEnd],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // Build clip path for center-outward wipe
  let clipPath: string;
  if (isLeft) {
    // Reveal from right edge (100%) toward left (0%)
    const leftEdge = (1 - revealProgress) * 100;
    clipPath = `inset(0 0 0 ${leftEdge}%)`;
  } else {
    // Reveal from left edge (0%) toward right (100%)
    const rightEdge = (1 - revealProgress) * 100;
    clipPath = `inset(0 ${rightEdge}% 0 0)`;
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: panelLeft,
        top: 0,
        width: panelWidth,
        height: CANVAS.height,
        overflow: 'hidden',
        clipPath,
      }}
    >
      {/* Video content with ken burns zoom */}
      <OffthreadVideo
        src={staticFile(videoSrc)}
        style={{
          position: 'absolute',
          top: '50%',
          left: '50%',
          transform: `translate(-50%, -50%) scale(${zoom})`,
          minWidth: '100%',
          minHeight: '100%',
          objectFit: 'cover',
        }}
        muted
      />

      {/* Inner vignette on the panel edge closest to divider */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          [isLeft ? 'right' : 'left']: 0,
          width: DIMENSIONS.vignetteWidth,
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
