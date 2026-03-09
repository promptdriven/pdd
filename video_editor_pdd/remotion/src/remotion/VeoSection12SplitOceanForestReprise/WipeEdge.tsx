import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { CANVAS, COLORS, WIPE, ANIMATION } from './constants';

interface WipeEdgeProps {
  wipeX: number;
}

export const WipeEdge: React.FC<WipeEdgeProps> = ({ wipeX }) => {
  const frame = useCurrentFrame();

  // Glow fades out during frames 85-90
  const glowOpacity = interpolate(
    frame,
    [ANIMATION.glowFadeStart, ANIMATION.glowFadeEnd],
    [1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Hide edge when fully off-screen right
  if (wipeX >= CANVAS.width && glowOpacity <= 0) return null;

  return (
    <>
      {/* Soft amber glow trailing the wipe (left side) */}
      <div
        style={{
          position: 'absolute',
          left: wipeX - WIPE.glowWidth,
          top: 0,
          width: WIPE.glowWidth,
          height: CANVAS.height,
          background: `linear-gradient(to right, transparent, ${COLORS.wipeGlow})`,
          opacity: glowOpacity,
          zIndex: 5,
        }}
      />

      {/* White wipe edge line */}
      <div
        style={{
          position: 'absolute',
          left: wipeX - WIPE.edgeWidth / 2,
          top: 0,
          width: WIPE.edgeWidth,
          height: CANVAS.height,
          background: `linear-gradient(to right, ${COLORS.wipeEdge}, transparent)`,
          opacity: glowOpacity,
          zIndex: 6,
        }}
      />
    </>
  );
};
